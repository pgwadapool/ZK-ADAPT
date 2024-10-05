# Secure Multi-Party Key Generation and Gradient Encryption with ZKP

This repository provides implementations for **Key Generation Schemes** (Trusted Key Generation and Distributed Key Generation) and a program for **encrypting and decrypting gradients** along with **Zero-Knowledge Proof (ZKP)**. These components are designed to support secure multi-party computation scenarios, such as in federated learning, where participants collaboratively encrypt, prove, and decrypt gradients while ensuring privacy and security.

## Available Key Generation Schemes

### 1. Trusted Key Generation Center (KGC)
In the **Trusted Key Generation Center (KGC)** scheme, a trusted central authority generates the Paillier keypair and distributes secret shares of the private key components (`p` and `q`) to participants using **Additive Secret Sharing**. The public key is shared with all participants, and the private key can be reconstructed collaboratively by the participants when decryption is required.

#### Key Features:
- **Paillier keypair generation** with a shared public key.
- **Secret sharing** of the private key components using Additive Secret Sharing.
- Participants collaborate to decrypt encrypted data using their secret shares.

#### Use Case:
This scheme is suitable when a trusted authority is available to generate and distribute the keys securely. It is simple but relies on the security of the central key generator.

### 2. Distributed Key Generation (DKG)
The **Distributed Key Generation (DKG)** scheme eliminates the need for a trusted central authority. Instead, participants collaboratively generate the Paillier private key using **Shamir's Secret Sharing**. Each participant generates a random polynomial, and shares of the secret (private key) are exchanged among participants. A threshold number of participants is required to reconstruct the private key for decryption.

#### Key Features:
- No trusted third party is required.
- Each participant generates their own random polynomial, and shares are exchanged among participants.
- The private key is reconstructed using Lagrange interpolation, ensuring that only a subset of participants (threshold) can decrypt
- Refer to TNO MPC Lab - Protocols - Distributed Keygen 

#### Use Case:
This scheme is suitable when a trusted third party is not available, and participants want a fully decentralized key generation mechanism. However, it may lack the public verifiability features of more advanced schemes like Feldman VSS.

## Gradient Encryption, Decryption, and Zero-Knowledge Proof (ZKP)

This repository also includes a program to **encrypt, decrypt, and generate zero-knowledge proofs (ZKP)** for gradients. This is useful in secure multi-party computation (e.g., federated learning) where participants wish to collaboratively encrypt gradients, prove correctness, and decrypt the aggregated result while preserving privacy.

### Key Features:
- **Paillier Encryption**: Gradients are encrypted using the Paillier encryption scheme, which supports homomorphic operations.
- **Zero-Knowledge Proof (ZKP)**: The program generates and verifies ZKPs to ensure that the encrypted gradient is valid without revealing the actual gradient or the private key.
- **Threshold Decryption**: Participants decrypt the aggregated gradients using their secret shares of the private key.

### How It Works:
1. **Encrypt Gradients**: Each participant encrypts their gradients using the shared public key.
2. **Generate Zero-Knowledge Proof**: Each participant generates a ZKP to prove the correctness of the encrypted gradient.
3. **Collaborative Decryption**: After aggregation, participants provide their secret shares to decrypt the aggregated gradient using a threshold decryption mechanism.

## Choosing a Key Generation Scheme

Depending on your security model, you can choose one of the following key generation schemes:
- **Trusted Key Generation Center (KGC)**: If you have a trusted central authority to generate and distribute keys securely.
- **Distributed Key Generation (DKG)**: If you prefer a decentralized approach where participants collaboratively generate the keypair without needing a trusted third party.


**Choose a Key Generation Scheme:**
- For Trusted Key Generation, refer to the trusted_kg_helper.py file.
```
# Initialize KGC
kgc = KeyGenerationCenter()

# Generate and distribute keys
public_key = kgc.distribute_keys()
```

- For Distributed Key Generation, refer to the dkg_helper.py file.
```
# Initialize participants
participants = [DKGParticipant(i + 1, 5, 3) for i in range(5)]

# Each participant shares their secret
shared_secrets = {p.id: p.share_secret() for p in participants}

# Participants exchange shares and reconstruct the secret
subset_of_participants = random.sample(participants, 3)
shares_to_reconstruct = {p.id: p.shares_received[p.id] for p in subset_of_participants}
reconstructed_secret = subset_of_participants[0].reconstruct_secret(shares_to_reconstruct)
```
  
**Run the Gradient Encryption and ZKP Program:**

Refer to the ThresholdPallierZkp.py file to run the program for encrypting and decrypting gradients with ZKP.


# WorkFlow
1. Particpants agree on training requirements. They exhcange keys and decided on how to generate Pailler Keys. Use TNO from Pet Labs or check the crypto/experimental folder for referece code
2. Start Hydra Head. Look at Hydra.family to start hydra head
3. Once Head is initialized, then use Key generation and share the public keys needed for encryption etc. Look at the trusted_kg_helper.py or dkg_helper.py
4. Create Storj Storage. Have one bucket per participant with approriate permissions. Use Storj website
5. Start the training for one epoch. An example is mnnist_n.py
6. Encrypt the gradient and also the proof. tno_pallier_NIZKP.py/ThresholdPallierZkp.py/ThresholdPallierZkp.py. Use any one
7. Upload them to Stroj bucket. Look at storj_utils.py
8. Send a  transaction on hydra head to indicate epoch is completed. Look at hydra_messaging.py
9. Keep snooping for all other participant transaction This is also shown in hydra_messgaing.py
10. Once this is done repeat step 5 to 9.
11. After agreed spochs are done, send Close and Fanout transaction
12. If needed ensure periodically you update the key if using Additive secret sharing.


