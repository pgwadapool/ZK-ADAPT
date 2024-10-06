import asyncio
import websockets
import json
import subprocess
import aiohttp
"""
HydraClient Class

This class is designed to facilitate communication with a Hydra node over WebSocket,
performing operations related to UTXOs and transactions in a Cardano blockchain environment.

Usage:
1. Initialize the HydraClient with appropriate parameters:
   - `url`: WebSocket URL (default is "http://127.0.0.1:4001").
   - `address_file`: Path to the file containing the address for the client.
   - `output_address_file`: Path to the file containing the output address.
   - `lovelace_value`: The amount of lovelace to send in the transaction.
   - `threshold`: The minimum UTXO value required to proceed.

2. Call the `run()` method to start the client operations, which includes listening for messages
   from the WebSocket, executing commands, building and sending transactions.

Example:
```python
async def main():
    client = HydraClient(address_file="path/to/address.addr", output_address_file="path/to/output.addr", lovelace_value=5000000, threshold=1000000)
    await client.run()
"""
class HydraClient:
    def __init__(self, address_file: str, output_address_file: str, lovelace_value: int, threshold: int,url: str = "http://127.0.0.1:4001"):
        self.url = url
        self.address_file = address_file
        self.output_address_file = output_address_file
        self.lovelace_value = lovelace_value
        self.threshold = threshold
        self.head_is_open_received = asyncio.Event()
        self.ready_to_fanout_received = asyncio.Event()

    async def listen(self):
        async with websockets.connect(self.url.replace("http", "ws") + "/?history=no") as websocket:
            print("Connected to HydraClient")
            while True:
                message = await websocket.recv()
                await self.receive_message(message)

    async def receive_message(self, message: str):
        data = json.loads(message)
        if data.get("tag") == "HeadIsOpen":
            print("Received HeadIsOpen message:", data)
            self.head_is_open_received.set()
        elif data.get("tag") == "ReadyToFanout":
            print("Received ReadyToFanout message:", data)
            self.ready_to_fanout_received.set()
        else:
            print("Unexpected message:", data)

    async def send_message(self, message: str):
        async with websockets.connect(self.url.replace("http", "ws") + "/?history=no") as websocket:
            await websocket.send(message)

    async def execute_command(self, command: str):
        result = await asyncio.create_subprocess_shell(
            command,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE
        )
        stdout, stderr = await result.communicate()
        if result.returncode != 0:
            raise Exception(f"Error executing command: {stderr.decode().strip()}")
        return stdout.decode().strip()

    async def check_utxo(self):
        while True:
            async with aiohttp.ClientSession() as session:
                async with session.get(f"{self.url}/snapshot/utxo") as response:
                    print(f"Response status: {response.status}")
                    response_text = await response.text()

                    if response.status == 200:
                        try:
                            data = json.loads(response_text)
                            filtered_utxo = {k: v for k, v in data.items() if v["address"] == self.get_address()}
                            if filtered_utxo:
                                lovelace_value = list(filtered_utxo.values())[0]['value']['lovelace']
                                print(f"Lovelace value: {lovelace_value}")
                                if lovelace_value >= self.threshold:
                                    break
                        except json.JSONDecodeError:
                            print("Failed to decode JSON response.")
                            print(f"Response text: {response_text}")
                    else:
                        print(f"Unexpected response status: {response.status}")
                        print(f"Response text: {response_text}")

            await asyncio.sleep(5)

    def get_address(self):
        with open(self.address_file) as f:
            return f.read().strip()

    def get_output_address(self):
        with open(self.output_address_file) as f:
            return f.read().strip()

    async def handle_api_request(self, command: str, payload: dict = None):
        if command in ["Init", "Abort", "NewTx", "Decommit", "Close", "Contest", "Fanout"]:
            message = {"tag": command, "payload": payload}
            await self.send_message(json.dumps(message))
            response = await self.receive_response()  # Assuming you want to wait for a response
            return response

        elif command == "DraftCommitTxRequest":
            return await self.send_http_request("commit", payload)

        elif command == "GetUTxO":
            return await self.send_http_request("snapshot/utxo", payload)

        elif command == "DecommitRequest":
            return await self.send_http_request("decommit", payload)

        elif command == "getProtocolParameters":
            return await self.send_http_request("protocol-parameters", payload)

        elif command == "submitTxRequest":
            return await self.send_http_request("cardano-transaction", payload)

        else:
            raise ValueError(f"Unknown command: {command}")

    async def send_http_request(self, endpoint: str, payload: dict):
        url = f"{self.url}/{endpoint}"
        async with aiohttp.ClientSession() as session:
            async with session.post(url, json=payload) as response:
                response_data = await response.json()
                return response_data

    async def step_send_init(self):
        await self.handle_api_request("Init")

    async def step_execute_utxo_command(self):
        utxo_command = (
            f"curl -s {self.url}/snapshot/utxo "
            f"| jq \"with_entries(select(.value.address == \\\"$(cat {self.address_file})\\\"))\" "
            f"> utxo.json"
        )
        await self.execute_command(utxo_command)

    async def step_wait_for_head_is_open(self):
        await self.head_is_open_received.wait()
        print("Head is open")

    async def step_build_raw_transaction(self):
        build_command = (
            "cardano-cli conway transaction build-raw "
            f"--tx-in $(jq -r 'to_entries[0].key' < utxo.json) "
            f"--tx-out $(cat {self.output_address_file})+{self.lovelace_value} "
            f"--tx-out $(cat {self.address_file})+$(jq 'to_entries[0].value.value.lovelace - {self.lovelace_value}' < utxo.json) "
            "--fee 0 --out-file tx.json"
        )
        await self.execute_command(build_command)

    async def step_sign_transaction(self):
        sign_command = (
            "cardano-cli conway transaction sign "
            "--tx-body-file tx.json "
            f"--signing-key-file credentials/{self.address_file.split('/')[-1].replace('addr', 'sk')} "
            "--out-file tx-signed.json"
        )
        await self.execute_command(sign_command)

    async def step_send_signed_transaction(self):
        with open("tx-signed.json") as f:
            signed_tx = f.read()
            await self.handle_api_request("NewTx", {"transaction": signed_tx})
        print("Now waiting for UTXO")

    async def step_send_close(self):
        await self.handle_api_request("Close")

    async def step_wait_for_ready_to_fanout(self):
        await self.ready_to_fanout_received.wait()
        print("Now Fanout for UTXO")

    async def step_send_fanout(self):
        await self.handle_api_request("Fanout")

    async def run(self):
        # Start listening to the WebSocket in a separate task
        listener_task = asyncio.create_task(self.listen())

        await self.step_send_init()
        await self.step_execute_utxo_command()
        await self.step_wait_for_head_is_open()
        await self.step_build_raw_transaction()
        await self.step_sign_transaction()
        await self.step_send_signed_transaction()
        await self.check_utxo()
        await self.step_send_close()
        await self.step_wait_for_ready_to_fanout()
        await self.step_send_fanout()

#Example usage
async def run_hydra_client():
    address_file = "credentials/alice-funds.addr"
    output_address_file = "credentials/bob-funds.addr"
    lovelace_value = 5000000
    threshold = 1000000
    hydra_client = HydraClient(address_file=address_file, output_address_file=output_address_file, lovelace_value=lovelace_value, threshold=threshold)
    await hydra_client.run()

if __name__ == "__main__":
    asyncio.run(run_hydra_client())
