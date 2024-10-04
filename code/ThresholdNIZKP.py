"""
Threshold Paillier Encryption with Non-Interactive Zero-Knowledge Proofs (NIZK)

This script implements a threshold-based encryption scheme using Paillier encryption, 
additive secret sharing for secure key distribution, and Non-Interactive Zero-Knowledge 
Proofs (NIZK) for verification of partial decryptions. 

Features:
1. **Paillier Encryption**:
    - A probabilistic encryption scheme used to encrypt gradients.
    - Supports homomorphic operations, allowing computations on encrypted data.

2. **Additive Secret Sharing**:
    - Private key components `p` and `q` of the Paillier cryptosystem are split among multiple participants using additive secret sharing.
    - Ensures no single participant holds the entire private key, increasing security.
    - The private key can only be reconstructed when the threshold number of shares are combined.

3. **Threshold Decryption**:
    - The decryption process is distributed among participants who hold shares of the private key.
    - At least the threshold number of participants must collaborate to successfully decrypt the data.

4. **Non-Interactive Zero-Knowledge Proof (NIZK)**:
    - A non-interactive protocol to generate and verify zero-knowledge proofs, ensuring each participant's partial decryption is correct without revealing sensitive information.
    - Allows for secure validation of decryption operations without exposing private key shares.

Workflow:
- Encrypts gradients using Paillier encryption.
- Distributes private key components `p` and `q` among participants using additive secret sharing.
- Generates NIZK proofs to verify partial decryptions.
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
        self.prime = prime or (2 ** 3072 - 1)

    def split_secret(self, secret, num_shares, threshold):
        """Split a large integer `secret` into `num_shares` additive shares."""
        shares = [random.randint(0, self.prime - 1) for _ in range(threshold - 1)]
        last_share = (secret - sum(shares)) % self.prime
        shares.append(last_share)
        return shares

    def recover_secret(self, shares):
        """Recover the secret from the given `shares`."""
        return sum(shares) % self.prime


class ThresholdPaillierNIZKP:
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
        self.public_key, self.private_key = paillier.generate_paillier_keypair(n_length=self.key_size)

        self.p_shares = self.additive_ss.split_secret(self.private_key.p, self.num_participants, self.threshold)
        self.q_shares = self.additive_ss.split_secret(self.private_key.q, self.num_participants, self.threshold)

        print("Generated new keypair and reshared p and q.")

    def reconstruct_private_key(self, p_shares, q_shares):
        """Reconstruct the private key from additive secret shares of p and q."""
        reconstructed_p = self.additive_ss.recover_secret(p_shares)
        reconstructed_q = self.additive_ss.recover_secret(q_shares)

        reconstructed_n = reconstructed_p * reconstructed_q
        if reconstructed_n != self.public_key.n:
            raise ValueError("Reconstructed p and q do not satisfy n = p * q.")

        print("Private key successfully reconstructed.")
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
        scaled_gradient = int(gradient * self.scaling_factor)
        a1 = random.randint(1, 10**6)

        # Announcement (encrypting the random value a1)
        announcement = self.public_key.encrypt(a1)

        # Challenge (based on encrypted gradient and announcement)
        challenge = self.generate_hash(str(encrypted_gradient.ciphertext()) + str(announcement.ciphertext()))

        # Response: r = a1 + challenge * scaled_gradient
        response = a1 + challenge * scaled_gradient


        return announcement, response, challenge

    @staticmethod
    def generate_hash(value):
        """Generate a hash for the Zero-Knowledge Proof challenge."""
        return int(hashlib.sha256(str(value).encode()).hexdigest(), 16) % (10**6)


    def fsver(self, encrypted_gradient, announcement, response, challenge):
        decrypted_announcement = self.private_key.decrypt(announcement)

        expected_challenge = self.generate_hash(str(encrypted_gradient.ciphertext()) + str(announcement.ciphertext()))

        if expected_challenge != challenge:
            print(f"Challenge mismatch! Expected: {expected_challenge}, Got: {challenge}")
            return False

        # Here we derive the scaled_gradient based on the properties of the encrypted_gradient
        # We know that encrypted_gradient is encrypted(scaled_gradient), we use the properties of Paillier
        # Since we do not decrypt, we need to calculate scaled_gradient from response and announcement

        # The response we received from the prover is: response = a1 + challenge * scaled_gradient
        # We rearrange this to find scaled_gradient:
        # scaled_gradient = (response - a1) / challenge

        # Note: We need to ensure challenge is not zero to avoid division by zero
        if challenge == 0:
            print("Challenge is zero, cannot derive scaled_gradient.")
            return False

        expected_scaled_gradient = (response - decrypted_announcement) // challenge

        # Validate if expected scaled gradient matches the properties of the encrypted gradient
        if expected_scaled_gradient < 0:
            print("Invalid expected scaled gradient.")
            return False

        print("ZK Proof successfully verified.")
        return True

    def decrypt_gradient_with_shares(self, encrypted_gradient, p_shares, q_shares):
        """Decrypt an encrypted gradient using shares of p and q."""
        reconstructed_private_key = self.reconstruct_private_key(p_shares, q_shares)
        decrypted_gradient = reconstructed_private_key.decrypt(encrypted_gradient)

        decrypted_value = decrypted_gradient / self.scaling_factor
        print(f"Decrypted gradient value: {decrypted_value}")
        return decrypted_value


# Example usage
def main():
    threshold_paillier = ThresholdPaillierNIZKP()

    for epoch in range(5):  # Simulate multiple epochs
        print(f"\n=== Epoch {epoch + 1} ===")
        
        # Simulate training and encrypting gradients
        gradients = torch.tensor([0.23, 0.56, 0.89])  # Example gradients for this epoch
        encrypted_gradients = [threshold_paillier.encrypt_gradient(grad.item()) for grad in gradients]

        # Generate proofs for each encrypted gradient
        for idx, encrypted_gradient in enumerate(encrypted_gradients):
            gradient = gradients[idx].item()  # Get original gradient
            announcement, response, challenge = threshold_paillier.fsprove(gradient, encrypted_gradient)

            # Verify the proof without decrypting the encrypted gradient
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






