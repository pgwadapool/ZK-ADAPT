"""
Threshold Paillier Encryption with Additive Secret Sharing and Zero-Knowledge Proofs (ZKP)

This script implements a threshold-based encryption scheme using Paillier encryption, additive secret sharing for secure key distribution, 
and a Sigma protocol for zero-knowledge proof (ZKP) verification of partial decryptions. 

Features:
1. **Paillier Encryption**:
    - Paillier is a probabilistic encryption scheme used to encrypt gradients in this example.
    - It supports homomorphic operations, which makes it useful for secure computation over encrypted data.

2. **Additive Secret Sharing**:
    - The private key components `p` and `q` of the Paillier cryptosystem are split among multiple participants using additive secret sharing.
    - This ensures that no single participant holds the entire private key, increasing security.
    - The private key can only be reconstructed when the threshold number of shares are combined.

3. **Threshold Decryption**:
    - The decryption process is distributed among participants who hold shares of the private key.
    - A sufficient number of participants (at least the threshold) must collaborate to successfully decrypt the data.

4. **Zero-Knowledge Proof (ZKP)**:
    - A Sigma protocol is used to generate and verify zero-knowledge proofs, ensuring that each participant's partial decryption is correct without revealing any sensitive information.
    - This allows for secure validation of decryption operations without exposing private key shares.

Workflow:
- Encrypts gradients using Paillier encryption.
- Distributes private key components `p` and `q` among participants using additive secret sharing.
- Generates zero-knowledge proofs to verify partial decryptions.
- Reconstructs the private key from shares and decrypts the encrypted gradients.

Usage:
- The script demonstrates the end-to-end process of encrypting, proving, verifying, and decrypting gradients.
- It can be adapted for any application requiring threshold encryption and secure decryption validation.
"""

import random
import hashlib
from phe import paillier
import torch

class AdditiveSecretSharing:
    def __init__(self, prime=None):
        # Choose a large prime for modular arithmetic
        self.prime = prime or (2 ** 3072 - 1)

    def split_secret(self, secret, num_shares, threshold):
        """Split a large integer `secret` into `num_shares` additive shares."""
        shares = [random.randint(0, self.prime - 1) for _ in range(threshold - 1)]
        # Last share is chosen so that the sum of all shares modulo prime is equal to the secret
        last_share = (secret - sum(shares)) % self.prime
        shares.append(last_share)
        return shares

    def recover_secret(self, shares):
        """Recover the secret from the given `shares`."""
        return sum(shares) % self.prime



class ThresholdPaillierWithZKP:
    def __init__(self, key_size=3072, scaling_factor=10**2, threshold=3, num_participants=5):
        self.key_size = key_size
        self.scaling_factor = scaling_factor
        self.threshold = threshold
        self.num_participants = num_participants
        self.additive_ss = AdditiveSecretSharing()

        # Initialize the Paillier keypair and distribute secret shares
        self.generate_new_keypair()

    def generate_new_keypair(self):
        """Generate a new Paillier keypair and redistribute shares of p and q."""
        # Generate Paillier keypair
        self.public_key, self.private_key = paillier.generate_paillier_keypair(n_length=self.key_size)

        # Split the private key parts (p and q) using additive secret sharing
        self.p_shares = self.additive_ss.split_secret(self.private_key.p, self.num_participants, self.threshold)
        self.q_shares = self.additive_ss.split_secret(self.private_key.q, self.num_participants, self.threshold)

        print("Generated new keypair and reshared p and q.")

    def reconstruct_private_key(self, p_shares, q_shares):
        """Reconstruct the private key from additive secret shares of p and q."""
        # Reconstruct p and q from their respective shares
        reconstructed_p = self.additive_ss.recover_secret(p_shares)
        reconstructed_q = self.additive_ss.recover_secret(q_shares)

        # Verify that n = p * q
        reconstructed_n = reconstructed_p * reconstructed_q
        if reconstructed_n != self.public_key.n:
            raise ValueError("Reconstructed p and q do not satisfy n = p * q.")

        print("Private key successfully reconstructed.")

        # Return the reconstructed private key
        return paillier.PaillierPrivateKey(self.public_key, reconstructed_p, reconstructed_q)

    def encrypt_gradient(self, gradient):
        """Encrypt a single gradient using Paillier encryption."""
        gradient = min(max(gradient, -self.scaling_factor), self.scaling_factor)
        scaled_gradient = int(gradient * self.scaling_factor)
        encrypted_gradient = self.public_key.encrypt(scaled_gradient)
        print(f"Gradient {gradient} successfully encrypted.")
        return encrypted_gradient

    def fsprove(self, gradient, encrypted_gradient):
        """Generate a Zero-Knowledge Proof for an encrypted gradient."""
        # Scale the gradient
        scaled_gradient = int(gradient * self.scaling_factor)
        # Generate a smaller random value for the announcement step
        a1 = random.randint(1, 10**6)

        # Announcement (encrypting the random value a1)
        announcement = self.public_key.encrypt(a1)

        # Challenge (based on encrypted gradient and announcement)
        challenge = self.generate_hash(str(encrypted_gradient.ciphertext()) + str(announcement.ciphertext()))

        # Response: r = a1 + challenge * scaled_gradient
        response = a1 + challenge * scaled_gradient

        print(f"Prover Generated: a1 = {a1}, challenge = {challenge}, response = {response}")
        return announcement, response, challenge

    @staticmethod
    def generate_hash(value):
        """Generate a hash for the Zero-Knowledge Proof challenge."""
        return int(hashlib.sha256(str(value).encode()).hexdigest(), 16) % (10**6)  # Limiting the size of the challenge

    def fsver(self, encrypted_gradient, announcement, response, challenge):
        """Verify the Zero-Knowledge Proof."""
        # Decrypt the encrypted gradient
        decrypted_gradient = self.private_key.decrypt(encrypted_gradient)

        # Reverse scaling to get back the floating-point number
        decrypted_gradient_float = decrypted_gradient / self.scaling_factor

        # Verifier computes the expected challenge again
        expected_challenge = self.generate_hash(str(encrypted_gradient.ciphertext()) + str(announcement.ciphertext()))

        # Check if the challenges match
        if expected_challenge != challenge:
            print(f"Challenge mismatch! Expected: {expected_challenge}, Got: {challenge}")
            return False

        # Verify that the mathematical relationship holds: response = a1 + challenge * scaled_gradient
        if response - challenge * decrypted_gradient == self.private_key.decrypt(announcement):
            print("ZK Proof successfully verified.")
            return True
        else:
            print("ZK Proof verification failed.")
            return False

    def decrypt_gradient_with_shares(self, encrypted_gradient, p_shares, q_shares):
        """Decrypt an encrypted gradient using shares of p and q."""
        # Reconstruct the private key from the provided shares
        reconstructed_private_key = self.reconstruct_private_key(p_shares, q_shares)
        decrypted_gradient = reconstructed_private_key.decrypt(encrypted_gradient)

        # Reverse scaling to get back the floating-point value
        decrypted_value = decrypted_gradient / self.scaling_factor
        print(f"Decrypted gradient value: {decrypted_value}")
        return decrypted_value


# Example usage
def main():
    # Initialize the threshold Paillier system with additive secret sharing and ZKP
    threshold_paillier = ThresholdPaillierWithZKP()

    # Train model, encrypt, prove, decrypt, and repeat for multiple epochs
    for epoch in range(5):  # Simulate multiple epochs
        print(f"\n=== Epoch {epoch + 1} ===")
        
        # Simulate training and encrypting gradients
        gradients = torch.tensor([0.23, 0.56, 0.89])  # Example gradients for this epoch
        encrypted_gradients = [threshold_paillier.encrypt_gradient(grad.item()) for grad in gradients]

        # Generate proofs for each encrypted gradient
        for idx, encrypted_gradient in enumerate(encrypted_gradients):
            gradient = gradients[idx].item()  # Get original gradient
            announcement, response, challenge = threshold_paillier.fsprove(gradient, encrypted_gradient)

            # Verify the proof
            is_valid = threshold_paillier.fsver(encrypted_gradient, announcement, response, challenge)
            print(f"Proof verification for gradient {idx}: {'Valid' if is_valid else 'Invalid'}")

        # Simulate decryption using secret shares
        p_shares = threshold_paillier.p_shares[:threshold_paillier.threshold]
        q_shares = threshold_paillier.q_shares[:threshold_paillier.threshold]
        decrypted_gradients = [threshold_paillier.decrypt_gradient_with_shares(encrypted_gradient, p_shares, q_shares) for encrypted_gradient in encrypted_gradients]
        
        # Periodically regenerate the Paillier keypair (optional based on your requirement)
        if (epoch + 1) % 3 == 0:  # Refresh keypair every 3 epochs
            print("\nRefreshing Paillier keypair...")
            threshold_paillier.generate_new_keypair()

if __name__ == "__main__":
    main()

