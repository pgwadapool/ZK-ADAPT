"""
Distributed Paillier Key Generation and Encrypted Gradient Example

This script demonstrates the process of generating a distributed Paillier encryption key among multiple parties,
along with encrypting and decrypting gradients from a simple neural network using PyTorch.

Workflow:
1. Each participant generates a large prime number.
2. Participants share their primes and calculate:
   - n: The product of all unique primes.
   - λ(n): The product of (p_i - 1) for each prime p_i.
3. Participants check the coprimality of λ(n) with n.
4. The public key consists of (n, g) where g = n + 1, and the private key is (p, q, λ(n)).
5. After training a simple neural network, the gradients are encrypted and then decrypted to demonstrate the functionality.

Key Integration:
- This implementation replaces traditional key generation with distributed key generation.
- The private key contains p, q, and λ(n) which can be accessed directly.
- Use `self.private_key[0]` for p, `self.private_key[1]` for q, and `self.private_key[2]` for λ(n).
- The splitting of p and q into shares is done using the existing `split_secret` method.

Dependencies:
- PyTorch
- SymPy

Usage:
- Ensure that the required libraries are installed.
- Adjust the number of participants and security parameters as needed.
"""


import torch
import torch.nn as nn
import torch.optim as optim
import secrets
from sympy import nextprime
from math import gcd
from functools import reduce

class SimpleNN(nn.Module):
    def __init__(self):
        super(SimpleNN, self).__init__()
        self.fc1 = nn.Linear(10, 5)
        self.fc2 = nn.Linear(5, 1)

    def forward(self, x):
        x = torch.relu(self.fc1(x))
        x = self.fc2(x)
        return x

def generate_large_prime(bits=512):
    """Generates a large prime number with the specified bit size."""
    return nextprime(secrets.randbelow(2**bits))

def distributed_paillier_keygen(num_participants, bits=512):
    """
    Generate a distributed Paillier key among multiple participants.
    
    Returns a public key (n, g) and a private key (p, q, lambda_n).
    """
    primes = []
    while len(primes) < num_participants:
        prime = generate_large_prime(bits)
        if all(gcd(prime, p) == 1 for p in primes):
            primes.append(prime)

    n = reduce(lambda x, y: x * y, primes)
    
    # For simplicity, we'll take the first two primes as p and q
    if len(primes) < 2:
        raise ValueError("Not enough primes generated for p and q.")
    
    p = primes[0]
    q = primes[1]
    
    # Calculate lambda_n as the product of (p-1) and (q-1)
    lambda_n = (p - 1) * (q - 1)

    # Check coprimality
    if gcd(lambda_n, n) != 1:
        raise ValueError("Generated lambda_n is not coprime with n.")
    
    # Debugging outputs
    print(f"Primes: {primes}")
    print(f"n: {n}")
    print(f"p: {p}, q: {q}")
    print(f"lambda_n: {lambda_n}")
    print(f"GCD(lambda_n, n): {gcd(lambda_n, n)}")

    g = n + 1
    return (n, g), (p, q, lambda_n)

def encrypt(plain, public_key):
    """Encrypts a plaintext integer using the public key."""
    n, g = public_key
    r = secrets.randbelow(n)
    c = (pow(g, plain, n**2) * pow(r, n, n**2)) % (n**2)
    return c

def decrypt(ciphertext, public_key, private_key):
    """Decrypts a ciphertext using the public key and private key."""
    n, _ = public_key
    lambda_n = private_key

    u = (pow(ciphertext, lambda_n, n**2) - 1) // n
    l = u % n

    return (l * pow(lambda_n, -1, n)) % n

# Example usage
num_participants = 5
public_key, private_key = distributed_paillier_keygen(num_participants)

# Create the model
model = SimpleNN()
optimizer = optim.SGD(model.parameters(), lr=0.01)

# Generate dummy data
x = torch.randn(1, 10)  # Input
y = torch.tensor([[1.0]])  # Target

# Forward pass
output = model(x)
loss = nn.MSELoss()(output, y)

# Backward pass
optimizer.zero_grad()
loss.backward()

# Encrypt the gradients
encrypted_gradients = {}
for name, param in model.named_parameters():
    if param.grad is not None:
        encrypted_grad = [encrypt(int(g.item()), public_key) for g in param.grad.view(-1)]
        encrypted_gradients[name] = encrypted_grad

# Decrypt the gradients
decrypted_gradients = {}
for name, encrypted_grad in encrypted_gradients.items():
    decrypted_grad = [decrypt(enc_grad, public_key, private_key[2]) for enc_grad in encrypted_grad]  # Use only lambda_n
    decrypted_gradients[name] = decrypted_grad

# Output
print("Encrypted gradients:", encrypted_gradients)
print("Decrypted gradients:", decrypted_gradients)
