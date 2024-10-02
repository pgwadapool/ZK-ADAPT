from phe import paillier
from secretsharing import SecretSharer
import torch
import math

class ThresholdPaillier:
    def __init__(self, key_size=3072, scaling_factor=10**2, threshold=3, num_participants=5):
        # Generate Paillier keypair
        self.public_key, self.private_key = paillier.generate_paillier_keypair(n_length=key_size)
        self.scaling_factor = scaling_factor
        self.threshold = threshold
        self.num_participants = num_participants

        # Split the private key parts (p and q) into smaller chunks and apply Shamir's Secret Sharing
        self.p_shares, self.q_shares = self.split_private_key_into_chunks()

    def split_private_key_into_chunks(self, chunk_size=128):
        """Split both p and q of the private key into smaller chunks and apply Shamir's Secret Sharing."""
        # Convert the private key's `p` and `q` components to hexadecimal strings
        p_hex = hex(self.private_key.p)[2:]  # Remove '0x' prefix
        q_hex = hex(self.private_key.q)[2:]  # Remove '0x' prefix

        # Split the large hex strings into smaller chunks
        p_chunks = [p_hex[i:i + chunk_size] for i in range(0, len(p_hex), chunk_size)]
        q_chunks = [q_hex[i:i + chunk_size] for i in range(0, len(q_hex), chunk_size)]

        # Apply Shamir's Secret Sharing to each chunk
        p_shares_per_chunk = [SecretSharer.split_secret(chunk, self.threshold, self.num_participants) for chunk in p_chunks]
        q_shares_per_chunk = [SecretSharer.split_secret(chunk, self.threshold, self.num_participants) for chunk in q_chunks]

        return p_shares_per_chunk, q_shares_per_chunk

    def reconstruct_private_key_from_chunks(self, p_shares_per_chunk, q_shares_per_chunk):
        """Reconstruct the private key from shares of each chunk."""
        # Reconstruct each chunk of p and q
        reconstructed_p_chunks = [SecretSharer.recover_secret(shares) for shares in p_shares_per_chunk]
        reconstructed_q_chunks = [SecretSharer.recover_secret(shares) for shares in q_shares_per_chunk]

        # Combine the chunks to form the full p and q hex values
        reconstructed_p_hex = ''.join(reconstructed_p_chunks)
        reconstructed_q_hex = ''.join(reconstructed_q_chunks)

        # Convert the reconstructed hex back to integers
        reconstructed_p = int(reconstructed_p_hex, 16)
        reconstructed_q = int(reconstructed_q_hex, 16)

        # Verify that n = p * q
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

    def decrypt_partial(self, encrypted_gradient, p_shares, q_shares):
        """Decrypt the gradient partially using a subset of private key shares."""
        # Reconstruct the private key from the given shares
        reconstructed_private_key = self.reconstruct_private_key_from_chunks(p_shares, q_shares)
        decrypted_gradient = reconstructed_private_key.decrypt(encrypted_gradient)
        return decrypted_gradient

    def decrypt_gradient_with_shares(self, encrypted_gradient, p_shares_per_chunk, q_shares_per_chunk):
        """Decrypt an encrypted gradient using shares of each chunk of p and q."""
        # Reconstruct private key from shares of each chunk
        reconstructed_private_key = self.reconstruct_private_key_from_chunks(p_shares_per_chunk, q_shares_per_chunk)
        decrypted_gradient = reconstructed_private_key.decrypt(encrypted_gradient)
        decrypted_value = decrypted_gradient / self.scaling_factor
        print(f"Decrypted gradient value: {decrypted_value}")
        return decrypted_value


# Example usage
def main():
    # Initialize the threshold Paillier system
    threshold_paillier = ThresholdPaillier()

    # Simulate saving gradients to a file using torch
    gradients = torch.tensor([0.23, 0.56, 0.89])  # Example gradients
    file_path = "gradients.pth"
    torch.save(gradients, file_path)
    
    # Load and encrypt gradients from file
    encrypted_gradients = []
    for grad in gradients:
        encrypted_grad = threshold_paillier.encrypt_gradient(grad.item())
        encrypted_gradients.append(encrypted_grad)

    # Select participant shares for p and q (use the first threshold shares for this demo)
    p_shares_per_chunk = [chunk[:threshold_paillier.threshold] for chunk in threshold_paillier.p_shares]
    q_shares_per_chunk = [chunk[:threshold_paillier.threshold] for chunk in threshold_paillier.q_shares]
    
    # Decrypt the gradients using the shares
    decrypted_gradients = []
    for encrypted_gradient in encrypted_gradients:
        decrypted_gradient = threshold_paillier.decrypt_gradient_with_shares(encrypted_gradient, p_shares_per_chunk, q_shares_per_chunk)
        decrypted_gradients.append(decrypted_gradient)
    
    print(f"Decrypted gradients: {decrypted_gradients}")

if __name__ == "__main__":
    main()

