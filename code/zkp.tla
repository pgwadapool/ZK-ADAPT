---- MODULE GradientEncryption ----
EXTENDS Integers, TLC, Sequences

(* Constants *)
SCALING_FACTOR == 10^6

(* Type Definitions *)
TypeInvariant == 
    /\ public_key \in [n \in Nat] -> Nat
    /\ private_key \in [n \in Nat] -> Nat
    /\ gradient \in Real
    /\ encrypted_gradient \in [ciphertext \in Nat] -> Nat
    /\ announcement \in [ciphertext \in Nat] -> Nat
    /\ response \in Nat
    /\ challenge \in Nat

(* Variables *)
VARIABLES public_key, private_key, gradient, encrypted_gradient, announcement, response, challenge

(* Initial State *)
Init == 
    /\ public_key = GenerateKeyPair()
    /\ private_key = GetPrivateKey(public_key)
    /\ gradient = 42.789
    /\ encrypted_gradient = EncryptGradient(public_key, gradient)
    /\ announcement = 0
    /\ response = 0
    /\ challenge = 0

(* Encrypt the gradient using Paillier Encryption *)
EncryptGradient(pk, g) == 
    LET scaled_gradient == CAST(g * SCALING_FACTOR, Nat) IN
    pk.encrypt(scaled_gradient)

(* Hash function for generating the challenge *)
Hash(value1, value2) == 
    (value1 + value2) % (10^6)  (* Simplified hash function *)

(* Generate a random integer *)
Random(min, max) == 
    min + (max - min) * RandomReal()

(* Sigma Protocol - Proof Generation *)
FsProve == 
    /\ announcement' = Encrypt(public_key, Random(1, public_key.n // 2))
    /\ challenge' = Hash(encrypted_gradient.ciphertext, announcement')
    /\ response' = announcement' + challenge' * CAST(gradient * SCALING_FACTOR, Nat)

(* Sigma Protocol - Proof Verification *)
FsVer == 
    /\ IF challenge' = Hash(encrypted_gradient.ciphertext, announcement) THEN
        /\ decrypted_gradient == private_key.decrypt(encrypted_gradient)
        /\ expected_response == announcement + challenge * CAST(decrypted_gradient, Nat)
        /\ response' = expected_response

(* Next State *)
Next == 
    \/ FsProve
    \/ FsVer

(* Temporal Properties *)
Spec == Init /\ [][Next]_(<<public_key, private_key, gradient, encrypted_gradient, announcement, response, challenge>>)

====

(* Helper Functions *)

GenerateKeyPair() == 
    [n |-> 100]  (* Placeholder for public key generation *)

GetPrivateKey(pk) == 
    [n |-> pk.n * 2]  (* Placeholder for deriving private key *)

Encrypt(pk, value) == 
    [ciphertext |-> value + pk.n]  (* Simplified encryption *)

(* Utility to generate a random real number *)
RandomReal() == 
    0.1  (* Placeholder for a random float between 0 and 1 *)

