# helpful APIs to 
# 1) encrypt the gradients using partial homomorphic encryption (phe). 
# 2) Sigma Protocol (Proof generation and Proof verification
# sample usage is provided. 

import random
from phe import paillier
import hashlib

# Paillier Encryption Setup
def paillier_keygen():
    public_key, private_key = paillier.generate_paillier_keypair()
    return public_key, private_key

# Scaling factor for floating-point numbers
SCALING_FACTOR = 10**6  # Adjust this as needed based on precision

# Encrypt Gradient using Paillier Encryption (with scaling for floating-point)
def encrypt_gradient(public_key, gradient):
    # Scale the gradient to an integer
    scaled_gradient = int(gradient * SCALING_FACTOR)
    encrypted_gradient = public_key.encrypt(scaled_gradient)
    return encrypted_gradient

# Hash function for generating the challenge, with a limit
def generate_hash(value):
    # Ensure the hash is limited to a smaller integer range
    return int(hashlib.sha256(str(value).encode()).hexdigest(), 16) % (10**6)  # Limiting the size of challenge

# Sigma Protocol - Proof Generation (fsprove)
def fsprove(public_key, gradient, encrypted_gradient):
    # Scale down the gradient if necessary (to avoid large numbers)
    scaled_gradient = int(gradient * SCALING_FACTOR)

    # Random value for announcement step
    a1 = random.randint(1, public_key.n // 2)  # Ensure a1 is not too large

    # Announcement (encrypting the random value a1)
    announcement = public_key.encrypt(a1)

    # Challenge (based on encrypted gradient and announcement)
    challenge = generate_hash(str(encrypted_gradient.ciphertext()) + str(announcement.ciphertext()))

    # Response: r = a1 + challenge * scaled_gradient
    response = a1 + challenge * scaled_gradient

    print(f"Prover Generated: a1 = {a1}, challenge = {challenge}, response = {response}")

    return announcement, response, challenge

# Sigma Protocol - Proof Verification (fsver)
def fsver(public_key, private_key, encrypted_gradient, announcement, response, challenge):
    # Decrypt the encrypted gradient using the private key
    decrypted_gradient = private_key.decrypt(encrypted_gradient)

    # Reverse scaling to get back the floating-point number
    decrypted_gradient_float = decrypted_gradient / SCALING_FACTOR

    # Verifier computes the expected challenge again (to ensure integrity)
    expected_challenge = generate_hash(str(encrypted_gradient.ciphertext()) + str(announcement.ciphertext()))

    # Check if the challenges match
    if expected_challenge != challenge:
        print(f"Challenge mismatch! Expected: {expected_challenge}, Got: {challenge}")
        return False

    # Verify that the mathematical relationship holds: response = a1 + challenge * scaled_gradient
    # Rearranged to check: response - challenge * decrypted_gradient == a1
    if response - challenge * decrypted_gradient == private_key.decrypt(announcement):
        return True
    else:
        print("Mathematical relation mismatch!")
        return False


# Example usage
def main():
    # Key Generation
    public_key, private_key = paillier_keygen()

    # Simulated floating-point gradient (e.g., from backpropagation)
    gradient = 42.789  # Example floating-point gradient

    # Encrypt the gradient
    encrypted_gradient = encrypt_gradient(public_key, gradient)

    # Generate ZK Proof (fsprove)
    announcement, response, challenge = fsprove(public_key, gradient, encrypted_gradient)

    # Verifier verifies the proof (fsver)
    is_valid = fsver(public_key, private_key, encrypted_gradient, announcement, response, challenge)

    # Output result
    if is_valid:
        print("Zero-Knowledge Proof verified: The encrypted gradient is valid.")
    else:
        print("Proof verification failed!")

if __name__ == "__main__":
    main()
