import torch
import torch.nn as nn
import torch.optim as optim
import torchvision
import torchvision.transforms as transforms
from storj_utils import upload_storj, download_storj

#This is a simple example to show Federated learning. After each round the weights are stored in Storj and downloaded. After aggregation the training starts again. 
# Number of parties and communication rounds are configurable

# Define a simple neural network
class SimpleNN(nn.Module):
    def __init__(self):
        super(SimpleNN, self).__init__()
        self.fc1 = nn.Linear(784, 128)  # Flatten MNIST images to a 784 long vector
        self.fc2 = nn.Linear(128, 10)

    def forward(self, x):
        x = torch.flatten(x, 1)
        x = torch.relu(self.fc1(x))
        x = self.fc2(x)
        return x

# Load and split MNIST data
def load_data(n_parties, dataset_size=None):
    transform = transforms.Compose([transforms.ToTensor(), transforms.Normalize((0.5,), (0.5,))])
    mnist = torchvision.datasets.MNIST(root='./data', train=True, download=True, transform=transform)
    
    if dataset_size is None:
        dataset_size = len(mnist) // n_parties

    # Split the dataset into n parts
    datasets = [torch.utils.data.Subset(mnist, range(i * dataset_size, (i + 1) * dataset_size)) for i in range(n_parties)]
    dataloaders = [torch.utils.data.DataLoader(ds, batch_size=64, shuffle=True) for ds in datasets]
    return dataloaders

# Training function
def train_model(model, dataloader):
    criterion = nn.CrossEntropyLoss()
    optimizer = optim.SGD(model.parameters(), lr=0.01, momentum=0.9)

    for epoch in range(1):
        for inputs, labels in dataloader:
            optimizer.zero_grad()
            outputs = model(inputs)
            loss = criterion(outputs, labels)
            loss.backward()
            optimizer.step()

    return model

# Save model to a file
def save_model(model, filename):
    torch.save(model.state_dict(), filename)

# Load model from a file
def load_model(model, filename):
    model.load_state_dict(torch.load(filename))
    return model

# Aggregate weights from multiple state_dicts
def aggregate_weights(state_dicts):
    aggregated_state_dict = {}
    for key in state_dicts[0]:
        aggregated_state_dict[key] = sum(state_dict[key] for state_dict in state_dicts) / len(state_dicts)
    return aggregated_state_dict

# Calculate accuracy of the model
def calculate_accuracy(model, test_set):
    testloader = torch.utils.data.DataLoader(test_set, batch_size=64, shuffle=False)
    correct = 0
    total = 0

    with torch.no_grad():
        for inputs, labels in testloader:
            outputs = model(inputs)
            _, predicted = torch.max(outputs.data, 1)
            total += labels.size(0)
            correct += (predicted == labels).sum().item()

    return 100 * correct / total

# Main execution
n_parties = 4  # Number of parties
trainloaders = load_data(n_parties)

models = [SimpleNN() for _ in range(n_parties)]

# Train each model on its respective data. j is communication rounds.
for j in range(5):
    print(f'Start of Training epoch {j}')
    for i, model in enumerate(models):
        models[i] = train_model(model, trainloaders[i])
        save_model(model, f'model_client{i}_state_dict.pt')
        upload_storj(f'model_client{i}_state_dict.pt', f"storj_path_{i}")

# Download and aggregate weights
    state_dicts = []
    for i in range(n_parties):
        download_storj(f"storj_path_{i}", f"Dmodel_client{i}_state_dict.pt")
        state_dicts.append(torch.load(f'Dmodel_client{i}_state_dict.pt'))

    test_set = torchvision.datasets.MNIST(root='./data', train=False, download=True, transform=transforms.ToTensor())
    for i, model in enumerate(models):
        accuracy = calculate_accuracy(model, test_set)
        print(f'Accuracy for client {i}: {accuracy}%')

    aggregated_state_dict = aggregate_weights(state_dicts)

    # Load aggregated weights into each model
    for model in models:
        model.load_state_dict(aggregated_state_dict)


    # Evaluate each model
    print("Accuracy for client After aggregation")
    for i, model in enumerate(models):
        accuracy = calculate_accuracy(model, test_set)
        print(f'Accuracy for client {i}: {accuracy}%')

print("Done with training")
