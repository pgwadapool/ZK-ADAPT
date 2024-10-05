#Deprecated!
#use TNO MPC library
import torch
import secrets
from sympy import nextprime
from math import gcd
from functools import reduce

def generate_large_prime(bits=512):
    return nextprime(secrets.randbelow(2**bits))

def distributed_paillier_keygen(num_participants, bits=512):
    primes = []
    while len(primes) < num_participants:
        prime = generate_large_prime(bits)
        if all(gcd(prime, p) == 1 for p in primes):
            primes.append(prime)

    n = reduce(lambda x, y: x * y, primes)
    
    if len(primes) < 2:
        raise ValueError("Not enough primes generated for p and q.")
    
    p = primes[0]
    q = primes[1]
    lambda_n = (p - 1) * (q - 1)

    if gcd(lambda_n, n) != 1:
        raise ValueError("Generated lambda_n is not coprime with n.")
    
    g = n + 1
    return (n, g), (p, q, lambda_n)

def encrypt(plain, public_key):
    n, g = public_key
    r = secrets.randbelow(n)
    c = (pow(g, plain, n**2) * pow(r, n, n**2)) % (n**2)
    return c

def decrypt(ciphertext, public_key, lambda_n):
    n, _ = public_key
    print(f"Ciphertext: {ciphertext}")
    print(f"Lambda_n: {lambda_n}")

    u = (pow(ciphertext, lambda_n, n**2) - 1) // n
    print(f"Intermediate u: {u}")

    l = u % n
    print(f"Intermediate l: {l}")

    lambda_n_inv = pow(lambda_n, -1, n)
    print(f"Inverse of lambda_n: {lambda_n_inv}")

    decrypted_value = (l * lambda_n_inv) % n
    print(f"Decrypted value: {decrypted_value}")

    return decrypted_value

# Example usage
num_participants = 5
public_key, private_key = distributed_paillier_keygen(num_participants)

# Original gradient
original_gradients = torch.tensor([23], dtype=torch.float32)
print("Original gradients:", original_gradients.tolist())

# Encrypt the gradients
encrypted_gradients = [encrypt(int(grad.item()), public_key) for grad in original_gradients]
print("Encrypted gradients:", encrypted_gradients)

# Decrypt the gradients
decrypted_gradients = [decrypt(enc_grad, public_key, private_key[2]) for enc_grad in encrypted_gradients]
print("Decrypted gradients:", decrypted_gradients)

# Check if decrypted gradients match the original
for original, decrypted in zip(original_gradients, decrypted_gradients):
    print(f"Original: {original.item()}, Decrypted: {decrypted}")
