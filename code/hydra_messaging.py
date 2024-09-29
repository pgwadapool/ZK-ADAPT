"""
hydra_messaging.py

A WebSocket client for interacting with a Hydra node.

This class establishes a connection to a specified WebSocket URL and listens for incoming messages.
Currently, it processes the "Greetings" message and logs it to the console. Additional message
handling can be implemented as needed.

Usage:
    To use this class in another program, import it and create an instance with the desired WebSocket URL.
    Then, call the `listen` method to start receiving messages.

Example:
    from Hydra_messaging import Hydra_comm

    async def main():
        client = Hydra_comm("ws://your-websocket-url")
        await client.listen()

"""

import asyncio
import websockets
import json

class Hydra_comm:
    def __init__(self, url: str):
        self.url = url

    async def listen(self):
        async with websockets.connect(self.url + "?history=no") as websocket:
            print("Connected to Hydra_comm")
            while True:
                message = await websocket.recv()
                await self.receive_message(message)

    async def receive_message(self, message: str):
        data = json.loads(message)
        if data.get("tag") == "Greetings":
            print("Received Greetings message:", data)
            # Handle the Greetings message as needed
        else:
            print("Unexpected message:", data)

# To run the WebSocket client, use the following in another file:
# asyncio.run(Hydra_comm("ws://your-websocket-url").listen())
