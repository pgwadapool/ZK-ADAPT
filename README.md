# qLORADecentralizedML

## Overview
qLORADecentralizedML is a pioneering project that integrates Quantized Low-Rank Approximation (qLORA) with decentralized machine learning, focusing on the efficient and private training of large language models (LLM). This initiative aims to enhance computational efficiency, ensure data privacy, and facilitate secure communication in federated learning environments.

## Key Features
- **qLORA Integration:** Utilizes qLORA for optimizing neural network training, reducing computational complexity in Distributed learning.
- **Decentralized Storage:** Leverages Storj for secure, distributed storage of model weights, enhancing data privacy.
- **State Channel Communication:** Employs state channels, specifically focusing on Cardano Hydra, for efficient and secure communication among participants.


## Design Document
For detailed information about the methodologies, experimental setup, and results of this project, refer to our design document, which is the published paper on this topic. You can find it in the [design_docs](/design_docs) folder.


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


