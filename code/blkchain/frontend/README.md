# HydraClient Web Interface

This project provides a web-based interface for interacting with the HydraClient, a Python application designed to communicate with the Hydra protocol for blockchain transactions.


## Prerequisites

- Python 3.7 or higher
- `aiohttp` and `Flask` libraries

You can install the required libraries using pip:

```bash
pip install Flask aiohttp
```

## Running the application

1. Make sure your HydraClient implementation (hydra_client.py) is functioning correctly.
2. run app.py
``` bash
python3 app.py
```
3. Open your web browser and go to http://127.0.0.1:5000/ to access the HydraClient web interface.


## Using the Interface

### Initialize HydraClient

1. **Fill in the following fields:**

    From Address File: Path to the address file containing the user's address.
    
    To Address File: Path to the address file for the output address.
    
    Lovelace Value: The amount of lovelace to be used in transactions.
    
    2. **Click the Initialize button to set up the HydraClient.**

3. **Send Command**
Fill in the Command field with one of the following commands:

    a. Init
    
    b. Abort
    
    c. NewTx
    
    d. Decommit
    
    e. Close
    
    f. Contest
    
    g. Fanout
    
    h. DraftCommitTxRequest
    
    i. GetUTxO
    
    j. DecommitRequest
    
    k. getProtocolParameters

l. submitTxRequest

Optionally, provide a JSON payload in the Payload field if the command requires additional data.

Click the Send Command button to execute the command.

4. **Response**

The server's response will be displayed below the forms, showing the status or any error messages.

```
+---------------------------------------------------+
|                   HydraClient GUI                  |
+---------------------------------------------------+
| Address File: [__________________________]        |
| Output Address File: [_____________________]       |
| Lovelace Value: [_________________________]        |
|                                                   |
|                [ Initialize ]                     |
+---------------------------------------------------+
|                                                   |
| Command: [______________________________]         |
| Payload: [______________________________]         |
|                                                   |
|                [ Send Command ]                   |
+---------------------------------------------------+
| Response:                                         |
| +-----------------------------------------------+ |
| |                                               | |
| |   (Response messages will appear here)       | |
| |                                               | |
| +-----------------------------------------------+ |
+---------------------------------------------------+

```

### Description of Interface Components

- **Address File**: Input field for the path to the address file.
- **Output Address File**: Input field for the path to the output address file.
- **Lovelace Value**: Input field for the amount of lovelace to be used.
- **Initialize**: Button to initialize the HydraClient with the provided information.
- **Command**: Input field for entering the command to be executed.
- **Payload**: Input field for any additional JSON data required by the command.
- **Send Command**: Button to send the specified command and payload to the HydraClient.
- **Response**: Area where the server's response or any error messages will be displayed.

This layout provides a simple yet functional interface for users to interact with the HydraClient.

