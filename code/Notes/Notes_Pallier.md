# Threshold Paillier Encryption with Shamir's Secret Sharing

This project implements a threshold Paillier encryption scheme using Shamir's Secret Sharing to split and securely share the Paillier private key among multiple participants. This enables secure collaborative decryption, where multiple parties can decrypt an encrypted gradient using partial decryption shares, without reconstructing the entire private key.

# Features

# Paillier encryption for encrypting and decrypting gradients.
Shamir's Secret Sharing to split and securely distribute the Paillier private key components (p and q) among participants.
Threshold decryption: A threshold number of participants (using their private key shares) can collaborate to decrypt the encrypted data.
Support for large secrets by splitting the Paillier key components (p and q) into smaller manageable chunks and applying Shamir’s Secret Sharing to each chunk.
Project Structure

# ThresholdPaillier class: Implements the threshold Paillier encryption scheme.

Main steps:
Key generation: Generate a Paillier keypair and split the private key into shares.
Encryption: Encrypt gradients using the Paillier public key.
Decryption: Decrypt the encrypted gradients by combining partial decryptions from multiple participants using their private key shares.
Installation

# Clone the repository:
```
git clone 
```
## Install dependencies:
```
pip install phe secretsharing torch
```

# Usage

Run the Example
Main script: The main() function simulates encrypting and decrypting gradients using the threshold Paillier encryption scheme.
python main.py

# Code Overview

## ThresholdPaillier class:

init(): Generates the Paillier keypair and splits the private key using Shamir's Secret Sharing.

split_private_key_into_chunks(): Splits the large p and q components into smaller chunks and applies Shamir's Secret Sharing to each chunk.

reconstruct_private_key_from_chunks(): Reconstructs the Paillier private key from the shared chunks of p and q.

encrypt_gradient(): Encrypts the gradient using the Paillier public key.

decrypt_gradient_with_shares(): Decrypts the gradient using private key shares and combines the partial decryptions.

## Simulated Example:
Encrypts sample gradients, distributes the private key shares, and decrypts the gradients using a threshold number of private key shares.

## Key Example

The program encrypts gradients and demonstrates threshold decryption by reconstructing the private key from multiple participant shares:



# Example Usage
threshold_paillier = ThresholdPaillier()

gradients = torch.tensor([0.23, 0.56, 0.89])  # Example gradients

encrypted_gradients = [threshold_paillier.encrypt_gradient(grad.item()) for grad in gradients]

# Decrypt using threshold shares

```
p_shares = threshold_paillier.p_shares[:threshold_paillier.threshold]

q_shares = threshold_paillier.q_shares[:threshold_paillier.threshold]

decrypted_gradients = [threshold_paillier.decrypt_gradient_with_shares(encrypted_grad, p_shares, q_shares) for encrypted_grad in encrypted_gradients]
```

# Problems Fixed

1. Python 2 to Python 3 Transition (Fixing long and hex Encoding Issues)

Initially, the project encountered issues due to Python 2-style handling of large integers (e.g., the long type and encode('hex') methods). These were fixed by:

Replacing long with int: Python 3 handles large integers natively with int.

Replaced encode('hex'): In Python 3, hexadecimal conversion is done using binascii.hexlify().

2. Secret Too Long for Shamir's Secret Sharing

When using Shamir's Secret Sharing with very large secrets (such as the Paillier private key components p and q), the secretsharing library raised errors due to the length of the secrets:

Solution: We split the large Paillier key components into smaller chunks and applied Shamir's Secret Sharing to each chunk. This allowed us to securely share large secrets across participants while avoiding the size limitation of the library.

# Example of chunking p and q into smaller parts for secret sharing

```
p_chunks = [p_hex[i:i + chunk_size] for i in range(0, len(p_hex), chunk_size)]

p_shares_per_chunk = [SecretSharer.split_secret(chunk, threshold, num_participants) for chunk in p_chunks]
```

3. Reconstruction Issues

Another issue occurred when reconstructing the private key from Shamir's Secret Sharing shares, specifically ensuring that p * q = n. This was solved by properly reconstructing each chunk of p and q, combining them, and verifying that the reconstructed values matched the original modulus n.

# Example of verifying reconstructed p and q
```
reconstructed_n = reconstructed_p * reconstructed_q
if reconstructed_n != self.public_key.n:
    raise ValueError("Reconstructed p and q do not satisfy n = p * q.")
4. Handling Large Numbers in Python 3
Since Python 3 natively supports large integers, handling the large numbers like p and q (which are typically thousands of bits) was done efficiently by converting between hexadecimal strings and integers.
```
## Contributing

Feel free to contribute by submitting issues or pull requests. All contributions are welcome!


Let me know if you want any more details or adjustments to the README!
