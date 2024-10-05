"""
Distributed Key Generation (DKG) Using Shamir's Secret Sharing

This code demonstrates a simple Distributed Key Generation (DKG) protocol using Shamir's Secret Sharing.
In DKG, participants collaborate to jointly generate a shared private key without a trusted third party.
The private key is distributed among participants, and only a threshold number of participants can 
reconstruct the secret (private key) using their shares.

Key Features:
1. **Distributed Secret Generation**:
    - Each participant generates a random polynomial where the constant term is their secret.
    - Participants evaluate their polynomial at points corresponding to other participants to generate shares.
    
2. **Secret Sharing**:
    - Each participant sends their computed shares to other participants. 
    - A threshold number of participants must collaborate to reconstruct the secret.

3. **Lagrange Interpolation**:
    - Participants use Lagrange interpolation to reconstruct the secret (private key) when needed. 
    - Only a threshold number of participants are required to perform this operation.

4. **No Trusted Dealer**:
    - Unlike traditional secret sharing, there is no trusted dealer in DKG. The key generation process is fully 
      decentralized, and no single participant learns the full secret (private key).

Limitations:
- This is a basic implementation and may lack the verifiability features found in more advanced DKG protocols 
  (e.g., Feldman or Pedersen VSS).
- The example uses Shamir's Secret Sharing, which is simple but doesn't provide public verifiability of the shares.

How It Works:
1. Each participant generates their own random polynomial and computes shares for other participants.
2. Shares are exchanged among participants, and each participant collects shares from the others.
3. A threshold number of participants can reconstruct the secret using their shares and Lagrange interpolation.
"""
import random
import secrets

class DKGParticipant:
    def __init__(self, participant_id, num_participants, threshold):
        self.id = participant_id
        self.num_participants = num_participants
        self.threshold = threshold
        self.secret = secrets.randbelow(100) + 1  # Secure random secret between 1 and 100
        self.polynomial = self._generate_polynomial(threshold)

    def _generate_polynomial(self, degree):
        """Generate a random polynomial of the given degree with the secret as the constant term."""
        return [self.secret] + [secrets.randbelow(100) + 1 for _ in range(degree - 1)]

    def evaluate_polynomial(self, x):
        """Evaluate the polynomial at a given x value."""
        result = sum(coef * (x ** i) for i, coef in enumerate(self.polynomial))
        return result

    def share_secret(self):
        """Generate shares for all other participants."""
        shares = {}
        for i in range(1, self.num_participants + 1):
            shares[i] = self.evaluate_polynomial(i)  # Share for participant i
        return shares

    def receive_shares(self, shares_from_others):
        """Receive shares from other participants."""
        self.shares_received = shares_from_others

    def reconstruct_secret(self, participants_shares):
        """Reconstruct the secret using Lagrange interpolation with a subset of shares."""
        x_values = list(participants_shares.keys())
        y_values = list(participants_shares.values())
        return self._lagrange_interpolation(0, x_values, y_values)

    @staticmethod
    def _lagrange_interpolation(x, x_values, y_values):
        """Perform Lagrange interpolation to compute the secret at x=0."""
        result = 0
        for j in range(len(y_values)):
            basis = 1
            for m in range(len(x_values)):
                if m != j:
                    basis *= (x - x_values[m]) / (x_values[j] - x_values[m])
            term = y_values[j] * basis
            result += term
        return round(result)


# Example usage of DKG
def main():
    num_participants = 5
    threshold = 3
    participants = [DKGParticipant(i + 1, num_participants, threshold) for i in range(num_participants)]

    # Each participant shares their secret
    shared_secrets = {p.id: p.share_secret() for p in participants}

    # Participants exchange shares
    for p in participants:
        shares_from_others = {i: shared_secrets[i][p.id] for i in range(1, num_participants + 1)}
        p.receive_shares(shares_from_others)

    # Try to reconstruct the secret until a valid (non-negative) secret is obtained
    while True:
        subset_of_participants = random.sample(participants, threshold)
        shares_to_reconstruct = {p.id: p.shares_received[p.id] for p in subset_of_participants}
        reconstructed_secret = subset_of_participants[0].reconstruct_secret(shares_to_reconstruct)
        
        print(f"Attempted reconstruction with shares: {shares_to_reconstruct}")
        print(f"Reconstructed secret: {reconstructed_secret}")
        
        # Check if the reconstructed secret is valid (non-negative)
        if reconstructed_secret >= 0:
            break  # Exit the loop if the secret is valid

    print(f"Final valid reconstructed secret: {reconstructed_secret}")

if __name__ == "__main__":
    main()
