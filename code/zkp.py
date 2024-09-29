# helpful APIs to 
# 1) encrypt the gradients using partial homomorphic encryption (phe). 
# 2) Sigma Protocol (Proof generation and Proof verification
# sample usage is provided. 

import torch
import random
from phe import paillier
import hashlib

class ZKPPaillier:
    def __init__(self, key_size=3072, scaling_factor=10**2, clip_value=10.0):
        # Initialize key pair, scaling factor, and gradient clipping
        self.public_key, self.private_key = paillier.generate_paillier_keypair(n_length=key_size)
        self.scaling_factor = scaling_factor
        self.clip_value = clip_value
    
    def encrypt_gradient(self, gradient):
        """Encrypt a single gradient using Paillier encryption."""
        # Clip the gradient to prevent extremely large values
        gradient = min(max(gradient, -self.clip_value), self.clip_value)
        # Scale the gradient to an integer
        scaled_gradient = int(gradient * self.scaling_factor)
        encrypted_gradient = self.public_key.encrypt(scaled_gradient)
        return encrypted_gradient
    
    def decrypt_gradient(self, encrypted_gradient):
        """Decrypt a single encrypted gradient and return the original floating-point value."""
        decrypted_gradient = self.private_key.decrypt(encrypted_gradient)
        # Reverse scaling to get back the floating-point value
        return decrypted_gradient / self.scaling_factor
    
    @staticmethod
    def generate_hash(value):
        """Generate a hash for the Zero-Knowledge Proof challenge."""
        return int(hashlib.sha256(str(value).encode()).hexdigest(), 16) % (10**6)  # Limiting the size of the challenge
    
    def fsprove(self, gradient, encrypted_gradient):
        """Generate a Zero-Knowledge Proof for an encrypted gradient."""
        # Scale the gradient
        scaled_gradient = int(gradient * self.scaling_factor)
        # Generate a smaller random value for the announcement step
        a1 = random.randint(1, 10**6)  # Use a small range to prevent large a1 values
        
        # Announcement (encrypting the random value a1)
        announcement = self.public_key.encrypt(a1)
        
        # Challenge (based on encrypted gradient and announcement)
        challenge = self.generate_hash(str(encrypted_gradient.ciphertext()) + str(announcement.ciphertext()))
        
        # Response: r = a1 + challenge * scaled_gradient
        response = a1 + challenge * scaled_gradient
        
        print(f"Prover Generated: a1 = {a1}, challenge = {challenge}, response = {response}")
        return announcement, response, challenge
    
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
            return True
        else:
            print("Mathematical relation mismatch!")
            return False

    def load_and_encrypt_gradients(self, file_path):
        """Load gradients from a file and encrypt them."""
        # Load the gradients (assumes tensor format saved with torch.save)
        gradients = torch.load(file_path)
        
        # Encrypt each gradient
        encrypted_gradients = []
        for grad in gradients:
            encrypted_grad = self.encrypt_gradient(grad.item())
            encrypted_gradients.append(encrypted_grad)
        
        return encrypted_gradients

    def decrypt_gradients(self, encrypted_gradients):
        """Decrypt a list of encrypted gradients."""
        decrypted_gradients = []
        for encrypted_grad in encrypted_gradients:
            decrypted_grad = self.decrypt_gradient(encrypted_grad)
            decrypted_gradients.append(decrypted_grad)
        
        return decrypted_gradients


# Example usage
def main():
    # Initialize the ZKP Paillier object
    zkp = ZKPPaillier()

    # Simulate saving gradients to a file using torch
    gradients = torch.tensor([0.23, 0.56, 0.89])  # Example gradients
    file_path = "gradients.pth"
    torch.save(gradients, file_path)
    
    # Load and encrypt gradients from file
    encrypted_gradients = zkp.load_and_encrypt_gradients(file_path)
    
    # For each encrypted gradient, generate ZK Proof (fsprove)
    for idx, encrypted_gradient in enumerate(encrypted_gradients):
        gradient = gradients[idx].item()  # Get original gradient
        announcement, response, challenge = zkp.fsprove(gradient, encrypted_gradient)
        
        # Verifier verifies the proof (fsver)
        is_valid = zkp.fsver(encrypted_gradient, announcement, response, challenge)
        
        # Output result
        if is_valid:
            print(f"Zero-Knowledge Proof verified for gradient {idx}: The encrypted gradient is valid.")
        else:
            print(f"Proof verification failed for gradient {idx}!")
    
    # Decrypt the gradients to verify correctness
    decrypted_gradients = zkp.decrypt_gradients(encrypted_gradients)
    print(f"Decrypted gradients: {decrypted_gradients}")

if __name__ == "__main__":
    main()
