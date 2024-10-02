"""
Trusted Key Generation Center (KGC) for Paillier Encryption

This code simulates a trusted Key Generation Center (KGC) that generates a Paillier keypair and 
distributes secret shares of the private key components (p and q) to multiple participants using 
Additive Secret Sharing.

Key Features:
1. **Paillier Key Generation**:
    - The trusted KGC generates a Paillier keypair with a public key (n = p * q) used for encryption 
      and private key components (p, q) used for decryption.
    
2. **Secret Sharing**:
    - The private key components (p and q) are split into secret shares using additive secret sharing.
    - Each participant receives their own share of p and q, and a threshold number of participants 
      are required to collaborate to reconstruct the private key.

3. **Public Key Sharing**:
    - The public key (n) is distributed to all participants. They will use this key to encrypt data 
      (e.g., gradients in a secure federated learning setting).

4. **Decryption**:
    - When data needs to be decrypted, a threshold number of participants can collaborate by providing 
      their secret shares of p and q to reconstruct the private key and decrypt the data.

Limitations:
- The KGC is a trusted party, meaning participants must trust it to generate and distribute keys securely.
- If the KGC is compromised, the entire security of the system could be at risk.

How It Works:
1. The KGC generates the Paillier keypair and splits the private key using additive secret sharing.
2. The public key is distributed to all participants, and each participant receives their own secret shares of p and q.
3. Participants use the public key to encrypt data and collaborate to decrypt data using their secret shares.
"""

from phe import paillier

import random

class AdditiveSecretSharing:
    def __init__(self, prime=None):
        # Choose a large prime for modular arithmetic
        self.prime = prime or (2 ** 3072 - 1)

    def split_secret(self, secret, num_shares, threshold):
        """
        Split a large integer `secret` into `num_shares` additive shares.
        Ensures the exact number of shares are generated regardless of the threshold.
        """
        if threshold > num_shares:
            raise ValueError("Threshold cannot be greater than the number of shares.")

        # Generate random shares
        shares = [random.randint(0, self.prime - 1) for _ in range(num_shares - 1)]
        
        # The last share is chosen so that the sum of all shares modulo prime is equal to the secret
        last_share = (secret - sum(shares)) % self.prime
        shares.append(last_share)
        
        # Ensure the number of shares matches num_shares
        if len(shares) != num_shares:
            raise ValueError(f"Generated {len(shares)} shares, but expected {num_shares}.")
        
        return shares

    def recover_secret(self, shares):
        """
        Recover the secret from the given `shares` by summing them modulo `prime`.
        """
        return sum(shares) % self.prime

class KeyGenerationCenter:
    def __init__(self, key_size=3072, num_participants=5, threshold=3):
        self.key_size = key_size
        self.num_participants = num_participants
        self.threshold = threshold

    def generate_paillier_keypair(self):
        """Generate Paillier keypair and split p and q into secret shares."""
        # Generate the Paillier keypair
        public_key, private_key = paillier.generate_paillier_keypair(n_length=self.key_size)

        # Split the private key components p and q using additive secret sharing
        additive_ss = AdditiveSecretSharing()
        p_shares = additive_ss.split_secret(private_key.p, self.num_participants, self.threshold)
        q_shares = additive_ss.split_secret(private_key.q, self.num_participants, self.threshold)

        # Ensure that the number of shares matches the number of participants
        if len(p_shares) != self.num_participants or len(q_shares) != self.num_participants:
            raise ValueError("Number of shares does not match the number of participants.")

        # Return the public key and the secret shares for p and q
        return public_key, p_shares, q_shares

    def distribute_keys(self):
        """Simulate the distribution of keys and secret shares."""
        # Generate the Paillier keypair and secret shares
        public_key, p_shares, q_shares = self.generate_paillier_keypair()

        # Simulate sending the public key and secret shares to participants
        for participant in range(1, self.num_participants + 1):
            # Ensure the participant index exists in the shares list
            if participant - 1 < len(p_shares) and participant - 1 < len(q_shares):
                p_share = p_shares[participant - 1]
                q_share = q_shares[participant - 1]
                print(f"Distributed to participant {participant}:")
                print(f"  Public key: {public_key.n}")
                print(f"  p_share: {p_share}")
                print(f"  q_share: {q_share}")
            else:
                print(f"Error: Participant {participant} does not have a corresponding share.")

        # Return the public key (to be used for encryption by all parties)
        return public_key

# Example Key Generation and Distribution
def main():
    # Create the Key Generation Center (KGC)
    kgc = KeyGenerationCenter()

    # KGC generates and distributes the keys and shares
    public_key = kgc.distribute_keys()

    # All participants now have their public key and secret shares (simulated)
    print(f"\nPublic key (n) shared with all participants: {public_key.n}")

if __name__ == "__main__":
    main()

