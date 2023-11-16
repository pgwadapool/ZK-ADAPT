# Integrating qLORA with Distributed Learning: Leveraging Storj for Distributed Storage and Cardano Hydra for State Channels

## Abstract:
This paper presents a novel approach to Distributed learning by integrating the Quantized Low-Rank Approximation (qLORA) technique for efficient model training and deployment. We leverage Storj for decentralized storage of model weights and Cardano Hydra for secure and efficient state channel communication among participants. Our method addresses key challenges in Distributed learning, including computational efficiency, data privacy, and secure communication. Preliminary experiments using the MNIST dataset demonstrate the feasibility and potential benefits of our approach.

## 1. Introduction:
Distributed learning enables collaborative machine learning without direct data sharing, preserving data privacy and security. However, challenges such as computational inefficiency, data privacy, and secure communication remain. We propose an innovative solution that integrates qLORA with Distributed learning, utilizing Storj for distributed storage and Cardano Hydra for state channel communication. This paper outlines our approach and its potential to enhance Distributed learning frameworks.

## 2. Background:
### 2.1 qLORA:
qLORA optimizes neural network training by using low-rank approximation and quantization techniques. It reduces computational complexity and model size, making it ideal for Distributed learning scenarios

Quantized Low-Rank Approximation (qLORA) is a novel optimization technique designed to enhance neural network training by significantly reducing computational requirements and model storage needs. At its core, qLORA employs two main strategies: low-rank approximation and quantization. These methodologies are synergistically combined to streamline the training process and produce lightweight models without substantially compromising performance.
#### Low-Rank Approximation
Low-rank approximation is a mathematical method used to approximate a high-dimensional data set with a data set of significantly lower dimensionality. This is achieved by identifying and retaining the most influential factors or components of the data while discarding the rest as noise. In the context of neural networks, this involves approximating the weight matrices of layers with lower rank counterparts, which require less computational power to process and can lead to faster training times. The lower rank matrices capture the essence of the transformations learned during training, enabling the model to maintain a high level of accuracy.

#### Quantization
Quantization in machine learning is the process of mapping input values from a large set, often continuous or high in number, into output values in a (much) smaller set. In neural networks, quantization typically refers to the reduction of the precision of the weights, from floating-point representations to lower-bit representations. By converting the high precision weights to a fixed, smaller range of integers, qLORA dramatically decreases the model size. This is particularly beneficial for deployment in environments with limited storage and memory resources.

#### Trade-offs 
The key challenge with techniques like qLORA is balancing efficiency gains with the maintenance of model performance. Reducing the complexity of the model can lead to faster computation and lower resource use, but it must be done carefully to avoid significantly compromising the model's ability to understand and generate language accurately.

#### Applications
This approach is particularly relevant for deploying AI models in environments where computational resources are limited. For instance, running a language model on a smartphone or an edge device in IoT applications would benefit greatly from such optimization techniques.



### 2.2 Distributed Learning:
Distributed learning allows for decentralized machine learning, where multiple participants collaboratively train a model while keeping their data localized.

#### Definition and Core Concepts
Distributed learning is a paradigm of machine learning that facilitates the collaborative training of a model across multiple devices or systems, which are often geographically dispersed. Unlike centralized learning, where data is accumulated and processed in a single location, distributed learning enables the model to travel to the data source, thus allowing for training to occur locally on participants' devices. This approach inherently respects the privacy of the data since it remains in its original location, and only model updates are communicated between nodes.

#### Advantages of Distributed Learning
The primary advantage of distributed learning is the preservation of data privacy and security. Since data does not leave its original environment, the risks associated with data transfer and central storage are minimized. Moreover, distributed learning can lead to significant improvements in scalability and efficiency, as it allows for parallel processing across numerous devices, each contributing to the model's learning process.

#### Challenges and Considerations
Despite its advantages, distributed learning poses several challenges. The heterogeneity of devices in terms of computational power and data distribution can lead to inconsistencies and delays in model training. Furthermore, the need for coordination and communication between devices introduces complexity, especially when ensuring the integrity and security of the model updates. To address these issues, sophisticated algorithms and protocols are employed to manage synchronization, handle device failures, and mitigate security threats.

#### Applications in Real-World Scenarios
Distributed learning is particularly useful in scenarios where data is sensitive, such as in healthcare, finance, and personal devices. For instance, hospitals can collaborate to develop predictive models without sharing patient records, or smartphones can learn user preferences without uploading personal data to the cloud.


### 2.3 Storj:
Storj provides decentralized cloud storage, offering a secure and distributed way to store and access data, such as model weights in distributed learning.

#### Overview of Storj
Storj is an open-source platform that offers decentralized cloud storage solutions. It is designed to provide secure and distributed data storage by leveraging the excess capacity of disk space available across the globe. By decentralizing data storage, Storj enhances security, privacy, and data sovereignty compared to traditional centralized cloud storage services.

#### Architecture and Functionality
The architecture of Storj is built on a network of independent nodes, each contributing storage space to form a collective cloud. These nodes are operated by various individuals and entities, creating a robust and resilient ecosystem. Data stored on Storj is encrypted, split into smaller fragments, and distributed across multiple nodes, ensuring that no single node has access to the complete data, thus maintaining confidentiality.

#### Data Encryption and Distribution
Prior to upload, files are encrypted on the client's side to ensure that data remains private and secure. The distribution of encrypted fragments employs erasure coding, a method that adds redundancy and fault tolerance to the system. This means even if some nodes become unavailable, the complete data can still be reconstructed from the remaining fragments.

#### Access Control and Retrieval
Storj employs a unique model for access management, where the data owner retains control over who can access their files. Permission can be granted or revoked at any time, without compromising the security of the data. When data retrieval is necessary, the system locates the relevant fragments and reconstitutes them, decrypting the data for the end-user.


### 2.4 Cardano Hydra:
Cardano Hydra is an advanced scalability solution for the Cardano blockchain designed to enhance transaction throughput and reduce latency, making it a fitting infrastructure for high-frequency and high-volume operations in decentralized applications. Hydra achieves this while preserving the robust security and governance model of the underlying Cardano protocol.

#### Key Features of Cardano Hydra:

**Secure:** Hydra Heads, the state channels of the Hydra protocol, ensure that participants can interact with confidence, knowing they cannot lose funds unless explicitly authorized.

**Fast:** Hydra Heads allow for near-instantaneous transaction settlement, making the protocol suitable for applications requiring quick finality.

**Isomorphic:** This quality means that Hydra utilizes the same ledger model as the Cardano mainnet, ensuring that off-chain Hydra interactions are consistent with on-chain transactions, thus maintaining a seamless user experience.

By incorporating these capabilities, Hydra presents a scalable framework for distributed learning systems, where numerous transactions and data exchanges occur simultaneously

## 3. Methodology:
Our methodology is centered around a harmonious integration of Quantized Low-Rank Approximation (qLORA) into a federated learning framework to harness the benefits of decentralized storage and communication systems.

### qLORA Integration
We incorporate qLORA to compress and accelerate the learning process. By reducing the rank and quantizing the weights of neural networks, we ensure that the models are lightweight and possess lower computational complexity. This makes them suitable for the distributed nature of our framework, where models are trained locally on participants' devices.

### Storj for Storage
The qLORA-modified weights, characterized by their reduced size, are stored using Storj's decentralized cloud storage. This ensures that each participant's model weights are secured and maintained in privacy-compliant buckets. Storj's distributed nature also allows for quick and efficient retrieval and updates of these weights, crucial for iterative learning processes.
Each participant has a seperate bucket. The participant provides access to other parties.

### Cardano Hydra for Communication
To manage the communication between participant nodes, we leverage Cardano Hydra's state channels. These channels facilitate a high-throughput and low-latency communication layer that is necessary for the efficient exchange of model updates. The isomorphic properties of Hydra ensure that off-chain transactions mirror the security and ledger consistency of the Cardano mainnet.

The workflow is as follows
1) Parties agree on the parameters for training including the LLM to use and number of epochs etc.
2) Parties agree and create a Project in Storj. Each participant will create a seperate bucket. Architecture can change based on the needs of participant
3) Each of the parties then create an address on cardano node (if they dont have) and generate the Hydra keys.
4) Each participant shares their public key and their IP/host address
5) Using the information provided by all participants, the process of starting the head is inititated
6) Each party commits predetrmined Ada. If any party misbehaves then head can be closed by other party.
7) Once the head is initialized and ready to use, the parties start the training.
8) After every iteration, the parties store the weights in their respective buckets. They notify other participants by sending 1Ada.
9) Once each party receives from others, they aggregate the gradients by reading all buckets and then load their local model with these new weights.
10) if any time a party thinks there is a problem with training they can close the head.
11) Once predetmined epochs are complete the training terminates and any party can close the head.

In this first iteration there is no penalty for misbehaviour. The first iteration was proof of concept.

   
### Collaborative Learning Cycle
In practice, our methodology establishes a cyclical process where each participant node trains the model locally using qLORA, stores the updated weights in Storj, and then communicates these updates across the network via Hydra. This cycle repeats, with each iteration refining the model's accuracy and performance.


### 3.4 System Architecture:
<img width="853" alt="image" src="https://github.com/pgwadapool/qLORADecentralizedML/assets/85845340/104b12f6-04d7-413a-a51f-8a822b0354d8">




## 4. Implementation and Experimental Setup:
We implemented a proof-of-concept using the MNIST dataset. Two separate models were trained on different subsets of the dataset to simulate a Distributed learning environment.

### 4.1 Training Process:
Each model was trained locally using a subset of the MNIST dataset. Since this is a small model, qLora was not used. We select the popular MNIST dataset [72] which contains 55,000 training samples, 5,000 veri- fication samples and 10,000 test samples. Then, we split randomly this dataset into 10 equi-sized subsets, i.e., each contains 55,000/10 = 5,500 samples. Then, we conduct multiple training experiments with 2, 4 and 10.

| Parameter         | Value          |
|-------------------|----------------|
| No. of iterations | 1500           |
| No. of epochs     | 1              |
| Learning rate     | 0.5            |
| Minimal batch size| 64             |

### 4.2 Hardware and SW used
1) Hardware: 3xDesktops with each 16Gb RAM and 8core CPU.
2) SW: Hydra with cardano node for each parties. For 10 parties, multiple parties were run on same host.
3) ML training was done using pytorch
4) Storj communication was done using python_uplink from Storj 3rd party.
5) websocket was used by parties to communicate with hydra-node


## 5. Preliminary Results:
Using the MNIST dataset,In terms of training accuracy, we show that the more parties participate in collaborative training, the higher the training accuracy.

|parties            | Accuracy       | baseline |
|-------------------|----------------|----------       
| Party1            | 94.8%          |  91%     |
| Party2            | 95%            |  92%     |
| Party3            | 94.9%          |  91.8%   |

With 10 parties each of the parties were close to **99%** accuracy.


## 6. Conclusion and Future Work:
Our initial findings suggest that integrating qLORA with Distributed learning, coupled with Storj for storage and Cardano Hydra for communication, offers benefits. Future work will focus on 

Future work involves
1) Using Llama with qLora
2) Right now there are no ecrow contracts.
3) Use NFTs to allow more complex interactions between parties.

Points 2 and 3 above will help minimize trust among particiapnts. With escrow and tokens rules can be enforced and slashing of the deposit is possible. However this involves careful deliberation and use of advance cryptography.



## References:
1) Hydra.family
2) Storj https://docs.storj.io/node
3) QLoRA: Efficient Finetuning of Quantized LLMs: Tim Dettmers, Artidoro Pagnoni, Ari Holtzman, Luke Zettlemoyer
