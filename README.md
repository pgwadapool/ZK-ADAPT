# qLORADecentralizedML

## Overview
qLORADecentralizedML is a pioneering project that integrates Quantized Low-Rank Approximation (qLORA) with decentralized machine learning, focusing on the efficient and private training of large language models (LLM). This initiative aims to enhance computational efficiency, ensure data privacy, and facilitate secure communication in distributed learning environments.

## Key Features
- **qLORA Integration:** Utilizes qLORA for optimizing neural network training, reducing computational complexity in Distributed learning.
- **Decentralized Storage:** Leverages Storj for secure, distributed storage of model weights, enhancing data privacy.
- **State Channel Communication:** Employs state channels, specifically focusing on Cardano Hydra, for efficient and secure communication among participants.


## Design Document
For detailed information about the methodologies, experimental setup, and results of this project, refer to our design document, which is the published paper on this topic. You can find it in the [design_docs](/design_docs) folder.
For understanding Dropout and how to tackle please refer to the document [Dropout](/design_docs) folder 


### Prerequisites
- Cardano node (testnet)
- Hydra node
- Python and MNIST dataset
- Storj access

### Installation
Step-by-step guide on setting up the project environment.

**This will be updated later**

```bash
# Clone this repository and install the requirements.txt
# Following env variables have to be set for Storj access
MY_API_KEY
MY_SATELLITE
MY_BUCKET
MY_STORJ_UPLOAD_PATH
MY_ENCRYPTION_PASSPHRASE

# To run the sample example mnist (without hydra and encryption)
cd code
python3 mnist_n.py
```

Please Refer to design_docs/workflow.md to understand how to create a workflow with encryption and Hydra.

## File List

In code directory
1. **HydraInteraction.tla:** TLA+ of hydra interaction
2. **ThresholdPallierZkp.tla :** TLA+ specification for encryption and ZKP
3. **ThresholdNIZKP.tla** TLA+ specification for encryption and using Non-Interactibe ZKP
4. **design.tla :** Mulltiparty training TLA+
5. **zkp.tla:** TLA+ for ZKP

**Blockchain Communication**
1. **hydra_messaging.py:** his provides APIs and example of how to interact with Hydra once its opened.

**Storage Utils**
1. **storj_utils.py:** Utility to interact with Storj.

**Cryptography**
1. **tno_pallier_nizkp.py** Same as above but using third party key generation.This is using Pallier key generation and encrypt decrypt from TNO library pip install tno.mpc.encryption-schemes.paillier
2. **ThresholdPallierZkp.py:** This provides APIs and example of how to use Pallier Encryption and ZKP. In this additive secret sharing is used
3. **tno_pallier_nizkp is preferred.** ThresholdPallierZkp is for example understanding. If production quality is needed use TNO MPC for key generation also. https://github.com/TNO-MPC/protocols.distributed_keygen


**Example**
1. **mnist_n.py:** Bare Bone example to show how all pieces can be integrated. However for simplicity and reproducibility ZKP and Hydra are not enabled. Storj is enabled and you need to have Storj API key to run this

**Basic codes. These can be ignored**
1. **ThresholdNIZKP.py** Same functionality as above, the proof is verified non-interactively.
2. **hydra_interaction.py :** Reduntant file while i was trying sync communication. Can be ignored.
3. **dkg_helper.py:** This provides API for distributed key generation. This is needed if you want to override keys needed for ThresholdPallierZkp.
4. **trusted_kg_helper.py:**  This provides API for Trusted key generation. This is needed if you want to override keys needed for ThresholdPallierZkp.
5. **thresholdPallier_shamir.py:** This uses Shamir secret sharing instead of Additive secret sharing. Rest implementation is same as ThresholdPallierZkp. However this can have issues because of python setup
6. **zkp.py :** Standalone ZKP implemetation if needed without any encryption


 





**As you can see there is tremendous flexibility.**
1. You can choose if you want encryption. If needed you can also choose what type of key generation and also what type of secret sharing
2. You can choose if you want Hydra or not
3. You can choose if you want ZKP or not
4. Storj is mandatory


**Design Docs**
1. **Workflow.md :** This explains the work flow for building your pipeline.
2. **secret_sharing_choice.md :** Some notes about difference in secret sharing
3. **design.md :**  High level design
4. **dropout_design.md :**  This is for future implementation to handle malicios participants.


# Design Philosophy
## Dynamic Joining and Trustlessness:
In a decentralized environment, especially in blockchain-based systems, "dynamic joining" refers to the ability of parties to join the distributed learning process at different stages without pre-approval or centralized control.
This system needs to be "trustless," meaning that it doesn't rely on mutual trust between parties. Instead, trust is built through cryptographic verification and smart contract mechanisms, ensuring that all parties adhere to agreed-upon rules without needing to trust each other personally.

## Safety in Training LLMs:
When training Large Language Models, which are complex and powerful, safety becomes a paramount concern. This includes not just the security of the data and the learning process but also the integrity and reliability of the training outcomes.
Ensuring safety in such a context means establishing robust protocols that all parties must adhere to. This includes securing the data, maintaining the quality of the training process, and ensuring that the outcomes of the model are reliable and unbiased.

## Adherence to Escrow and Non-Dynamic Leaving:
To ensure commitment and prevent disruptions, parties are required to adhere to an escrow mechanism. This means they deposit a certain amount of funds (or tokens) as collateral, which can be forfeited if they do not comply with the established rules.
Preventing "dynamic leaving" (i.e., parties leaving the process at will) is crucial for maintaining the quality of training. If parties could leave anytime, it would make the training process unstable and could significantly degrade the quality of the model being trained.

Punishment for Sabotage and Premature Closure:
There is a risk that a party might try to sabotage the training process, for example, by prematurely closing the head (or session) in a Hydra-like protocol. This could be for various reasons, such as gaining a competitive advantage or disrupting the process for other participants.
To mitigate this, the design includes a punishment mechanism, where parties involved in such malicious activities can be penalized. This is where the kill token comes into play. If a head is closed prematurely, and it's deemed to be a sabotage attempt, the majority of participants can use their kill tokens to penalize the saboteur, typically by slashing their deposited funds.

In current implenentation we dont consider this.

## Overall Design Philosophy:


In summary, this design is about creating a distributed learning ecosystem that is open yet secure, encouraging positive collaboration while deterring. This balance is crucial for the successful and safe training of Large Language Models in a decentralized, blockchain-based environment.
