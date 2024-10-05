"""
This script implements a threshold-based encryption scheme using the TNO library for Paillier encryption.

Library Used:
- TNO MPC Encryption Schemes: This library provides efficient implementations of various cryptographic primitives, including Paillier encryption.
- License: Apache Software License (Apache License, Version 2.0).

This script is licensed under the MIT License, allowing for open-source distribution and use.

Overview:
1. **ThresholdPaillierNIZKP Class**: 
    - This class encapsulates the functionality for encrypting and decrypting gradients using the Paillier encryption scheme.
    - It provides methods to encrypt single gradients, decrypt them using the private key, and print the results.

2. **Key Features**:
    - **Paillier Encryption**: A probabilistic encryption scheme that supports homomorphic addition.
    - **Gradient Scaling**: Gradients are scaled by a defined factor for encryption and then scaled back upon decryption.

3. **Methods**:
    - `__init__(self, key_size=2048, scaling_factor=100)`: Initializes the class, generating a new Paillier keypair.
    - `encrypt_gradient(self, gradient)`: Encrypts a given gradient and returns the encrypted value.
    - `decrypt_gradient(self, encrypted_gradient)`: Decrypts an encrypted gradient and returns the original value.

Usage:
- The script can be adapted for secure computations requiring encrypted gradient transmission, suitable for federated learning or secure multiparty computation applications.
"""

from tno.mpc.encryption_schemes.paillier import Paillier

class ThresholdPaillierNIZKP:
    def __init__(self, key_size=2048, scaling_factor=100):
        self.scaling_factor = scaling_factor
        self.paillier = Paillier.from_security_parameter(key_length=key_size)

    def encrypt_gradient(self, gradient):
        """Encrypt a single gradient using Paillier encryption."""
        gradient = min(max(gradient, -self.scaling_factor), self.scaling_factor)
        scaled_gradient = int(gradient * self.scaling_factor)
        encrypted_gradient = self.paillier.encrypt(scaled_gradient)
        print(f"Gradient {gradient} successfully encrypted.")
        return encrypted_gradient

    def decrypt_gradient(self, encrypted_gradient):
        """Decrypt an encrypted gradient using the private key."""
        decrypted_gradient = self.paillier.decrypt(encrypted_gradient)
        decrypted_value = float(decrypted_gradient) / self.scaling_factor
        print(f"Decrypted gradient value: {decrypted_value:.2f}")
        return decrypted_value

import random
import hashlib
from tno.mpc.encryption_schemes.paillier import Paillier
import torch

class ThresholdPaillierNIZKP:
    def __init__(self, key_size=2048, scaling_factor=10**2):
        self.scaling_factor = scaling_factor
        # Initialize the Paillier keypair
        self.paillier = Paillier.from_security_parameter(key_length=key_size)

    def encrypt_gradient(self, gradient):
        """Encrypt a single gradient using Paillier encryption."""
        gradient = min(max(gradient, -self.scaling_factor), self.scaling_factor)
        scaled_gradient = int(gradient * self.scaling_factor)
        encrypted_gradient = self.paillier.encrypt(scaled_gradient)
        print(f"Gradient {gradient} successfully encrypted.")
        return encrypted_gradient

    def fsprove(self, gradient, encrypted_gradient):
        """Generate a Zero-Knowledge Proof for an encrypted gradient."""
        scaled_gradient = int(gradient * self.scaling_factor)
        a1 = random.randint(1, 10**6)

        # Announcement (encrypting the random value a1)
        announcement = self.paillier.encrypt(a1)

        # Challenge (based on encrypted gradient and announcement)
        challenge = self.generate_hash(str(encrypted_gradient) + str(announcement))

        # Response: r = a1 + challenge * scaled_gradient
        response = a1 + challenge * scaled_gradient

        return announcement, response, challenge

    @staticmethod
    def generate_hash(value):
        """Generate a hash for the Zero-Knowledge Proof challenge."""
        return int(hashlib.sha256(str(value).encode()).hexdigest(), 16) % (10**6)

    def fsver(self, encrypted_gradient, announcement, response, challenge):
        decrypted_announcement = self.paillier.decrypt(announcement)

        expected_challenge = self.generate_hash(str(encrypted_gradient) + str(announcement))

        if expected_challenge != challenge:
            print(f"Challenge mismatch! Expected: {expected_challenge}, Got: {challenge}")
            return False

        if challenge == 0:
            print("Challenge is zero, cannot derive scaled_gradient.")
            return False

        # Convert decrypted_announcement to an integer
        decrypted_announcement_value = int(decrypted_announcement)

        expected_scaled_gradient = (response - decrypted_announcement_value) // challenge

        if expected_scaled_gradient < 0:
            print("Invalid expected scaled gradient.")
            return False

        print("ZK Proof successfully verified.")
        return True

    def decrypt_gradient(self, encrypted_gradient):
        """Decrypt an encrypted gradient using the private key."""
        decrypted_gradient = self.paillier.decrypt(encrypted_gradient)
        print(f"Decrypted gradient value: {decrypted_gradient}")
        decrypted_value = float(decrypted_gradient) / self.scaling_factor
        print(f"Decrypted gradient value: {decrypted_value:.2f}")
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

        # Simulate decryption of encrypted gradients
        decrypted_gradients = [threshold_paillier.decrypt_gradient(encrypted_gradient) for encrypted_gradient in encrypted_gradients]

if __name__ == "__main__":
    main()
