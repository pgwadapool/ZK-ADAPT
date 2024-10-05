## design.tla ##


In this simplified TLA+ specification (design.tla) for distributed training:

1) We define two agents, Agent1 and Agent2, each with its own model (Agent1Model and Agent2Model). The goal is for both agents to train their models to match at the end of training.

2) We have a constant MaxEpochs that defines the maximum number of training epochs.

3) The Init operator specifies the initial state of the system, where both agents start with an initial model (set to 0 in this example).

4) The Agent1Update and Agent2Update operators represent how each agent updates its model during training epochs. These are intentionally kept simple for illustration.

5) The Train operator defines the overall system behavior during training. It initializes the system, and in each epoch, both agents update their models. At the end of training, we ensure that the models of both agents match.

6) The Properties operator specifies the properties we want to check. In this case, we check if the models of Agent1 and Agent2 match at the end of training.

7) We have not considered dropout in this design


## HydraInteraction.tla ##

The TLA+ module encapsulates the logic for opening and closing Hydra heads and handling transactions in a way that ensures the system's consistency and reliability. Key components of the specification include:

- **Websocket State (`websocketState`)**: Represents the connection state of each party.
- **Hydra Head State (`hydraHeadState`)**: Indicates whether the Hydra head is open or closed.
- **Transactions (`transactions`)**: Records the transactions made by the parties.

 **Actions Modeled**
 
- **`OpenHydraHead`**: Models opening the Hydra head.
- **`SendTransaction(party)`**: Represents a party sending a transaction to the Hydra head.
- **`CloseHydraHead`**: Models closing the Hydra head.

## zkp.tla Gradient Encryption and Zero-Knowledge Proofs in TLA+ ##

**Overview**

This project implements a zero-knowledge proof system for verifying encrypted gradients using Paillier homomorphic encryption. The main goal is to ensure the integrity of the encrypted gradients without revealing their actual values.

**Components**

The implementation is divided into several key components:

1. **Key Generation**: Generates a public and private key pair for encryption.
2. **Gradient Encryption**: Encrypts gradients using the Paillier encryption scheme.
3. **Zero-Knowledge Proof Protocol**: Implements the Sigma Protocol for proof generation and verification.
4. **Hashing**: A function to generate challenges for the zero-knowledge proof.

## Threshold ZKP 

**Key Generation:**

The action KeyGen generates the public_key and splits the private key into private_key_shares (one for each participant).

**Encryption:**

EncryptGradients(grad) models the encryption of a gradient. It appends the encrypted gradient to the list of encrypted_gradients.

**Partial Decryption:**

Each participant performs a partial decryption on an encrypted gradient. The partial decryption is stored in partial_decryptions.

**Combining Partial Decryptions:**
Once the threshold number of partial decryptions is reached, the action CombineDecryptions(enc_grad) combines the partial decryptions to recover the original gradient. If fewer than the threshold number of shares are present, CannotDecrypt(enc_grad) ensures no decryption happens.

**Invariants:**

ThresholdMet: This invariant ensures that a gradient is decrypted only if the threshold number of shares is reached.

NoPrematureDecryption: This invariant ensures that a gradient cannot be decrypted prematurely if fewer than the threshold number of shares is available.

## Usage

This specification can be used with the TLA+ Toolbox and its TLC Model Checker to verify the correctness of the modeled system behaviors, including concurrency, consistency, and proper management of Hydra head states and transactions.

### Running the Specification

1. **Install the TLA+ Toolbox**: Download and install from [TLA+ GitHub releases](https://github.com/tlaplus/tlaplus/releases).
2. **Open the Specification**: Load `HydraInteraction.tla` into the TLA+ Toolbox.
3. **Create a Model**: Define the model constants like `Parties` and `HydraHeadURL`.
4. **Run TLC**: Use the TLC Model Checker to explore the behavior of the specification and verify properties like absence of deadlocks and correctness of state transitions.

## Contributing

Contributions to the specification are welcome! If you have suggestions for improvements or have identified issues, please feel free to submit pull requests or open issues in the repository.


