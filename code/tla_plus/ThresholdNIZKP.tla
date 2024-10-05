----------------------------- MODULE ThresholdPaillierNIZKP -----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N \* Number of participants
CONSTANT Threshold \* Minimum number of shares to decrypt

VARIABLES
    \* The public key
    public_key,

    \* The private key (p and q components) split into shares
    private_key_shares,

    \* Encrypted gradients
    encrypted_gradients,

    \* Shares of partial decryptions
    partial_decryptions,

    \* The decrypted gradients (final result)
    decrypted_gradients,

    \* Zero-Knowledge Proof components (announcement, response, challenge)
    zk_proofs

\* Key Generation
KeyGen ==
    /\ public_key = "Public Key"
    /\ private_key_shares = [i \in 1..N |-> "Private Key Share for participant i"]

\* Encryption of gradients
EncryptGradients(grad) ==
    /\ encrypted_gradients' = Append(encrypted_gradients, "Encrypted " \o grad)
    /\ UNCHANGED <<public_key, private_key_shares, partial_decryptions, decrypted_gradients, zk_proofs>>

\* Zero-Knowledge Proof Generation
GenerateZKP(enc_grad) ==
    /\ zk_proofs' = [zk_proofs EXCEPT ![enc_grad] = "ZKP for " \o enc_grad]
    /\ UNCHANGED <<public_key, private_key_shares, encrypted_gradients, partial_decryptions, decrypted_gradients>>

\* Partial Decryption: Each participant contributes a partial decryption
PartialDecrypt(participant, enc_grad) ==
    /\ partial_decryptions' = [partial_decryptions EXCEPT ![participant] = "Partial Decryption " \o enc_grad]
    /\ UNCHANGED <<public_key, private_key_shares, encrypted_gradients, decrypted_gradients, zk_proofs>>

\* Decryption: Combining partial decryptions when threshold is met
CombineDecryptions(enc_grad) ==
    /\ Cardinality(PartialDecryptions(enc_grad)) >= Threshold
    /\ decrypted_gradients' = Append(decrypted_gradients, "Decrypted " \o enc_grad)
    /\ UNCHANGED <<public_key, private_key_shares, encrypted_gradients, partial_decryptions, zk_proofs>>

\* Ensures that less than the threshold number of participants cannot decrypt
CannotDecrypt(enc_grad) ==
    /\ Cardinality(PartialDecryptions(enc_grad)) < Threshold
    /\ decrypted_gradients' = decrypted_gradients
    /\ UNCHANGED <<public_key, private_key_shares, encrypted_gradients, partial_decryptions, zk_proofs>>

PartialDecryptions(enc_grad) ==
    { d \in DOMAIN partial_decryptions : partial_decryptions[d] = "Partial Decryption " \o enc_grad }

\* Action to simulate encryption, ZKP generation, partial decryption, and reconstruction
Next ==
    \/ \E grad \in encrypted_gradients : EncryptGradients(grad)
    \/ \E enc_grad \in encrypted_gradients : GenerateZKP(enc_grad)
    \/ \E participant \in 1..N, enc_grad \in encrypted_gradients : PartialDecrypt(participant, enc_grad)
    \/ \E enc_grad \in encrypted_gradients : IF Cardinality(PartialDecryptions(enc_grad)) >= Threshold THEN CombineDecryptions(enc_grad) ELSE CannotDecrypt(enc_grad)

\* Initialization
Init ==
    /\ public_key = ""
    /\ private_key_shares = [i \in 1..N |-> ""]
    /\ encrypted_gradients = <<>>
    /\ partial_decryptions = [i \in 1..N |-> ""]
    /\ decrypted_gradients = <<>>
    /\ zk_proofs = [enc_grad \in <<>> |-> ""]

\* Specification of the system
Spec == Init /\ [][Next]_<<public_key, private_key_shares, encrypted_gradients, partial_decryptions, decrypted_gradients, zk_proofs>>

===============================

\* Test invariants and properties
\* Ensure that decryption only happens if the threshold is met
ThresholdMet == \A enc_grad \in encrypted_gradients : Cardinality(PartialDecryptions(enc_grad)) >= Threshold => \E decrypted_grad \in decrypted_gradients : decrypted_grad = "Decrypted " \o enc_grad

\* Ensure no decryption if less than the threshold number of shares
NoPrematureDecryption == \A enc_grad \in encrypted_gradients : Cardinality(PartialDecryptions(enc_grad)) < Threshold => ~\E decrypted_grad \in decrypted_gradients : decrypted_grad = "Decrypted " \o enc_grad
