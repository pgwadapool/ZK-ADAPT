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

# To run the sample example mnist (without hydra)
cd code
python3 mnist_n.py
```


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

## Overall Design Philosophy:
The overarching goal of this design is to create a distributed learning environment that balances openness (dynamic joining) with accountability (escrow and punishment mechanisms).
By doing so, it aims to foster a collaborative yet secure space for training LLMs, ensuring that all participants are motivated not only to contribute positively but also to refrain from any actions that could harm the collective effort.

In summary, this design is about creating a distributed learning ecosystem that is open yet secure, encouraging positive collaboration while deterring and penalizing harmful actions. This balance is crucial for the successful and safe training of Large Language Models in a decentralized, blockchain-based environment.
