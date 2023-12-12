import websocket
import json
import threading

# Define functions for WebSocket events
def on_message(ws, message):
    print("Received from Hydra:", message)

def on_error(ws, error):
    print("Error from Hydra:", error)

def on_close(ws, close_status_code, close_msg):
    print("Hydra WebSocket closed")

def on_open(ws):
    # Define the message to send - this should be adapted to actual use-case
    message = {
        "type": "example_request",
        "data": {
            # Add the necessary request data here
        }
    }
    send_message_to_hydra(ws, message)

# Function to send a message to the Hydra Head
def send_message_to_hydra(ws, message):
    json_message = json.dumps(message)
    ws.send(json_message)
    print("Sent to Hydra:", json_message)

# Function to initiate Hydra transaction
def initiate_hydra_transaction():
    ws_url = "ws://localhost:4001"  # Replace with actual Hydra Head URL

    # Create a WebSocket client and connect to the Hydra Head
    ws = websocket.WebSocketApp(ws_url, on_open=on_open, on_message=on_message,
                                on_error=on_error, on_close=on_close)

    # Start the WebSocket client in a new thread
    ws_thread = threading.Thread(target=ws.run_forever)
    ws_thread.start()
