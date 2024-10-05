import asyncio
import websockets
import json
import subprocess
import aiohttp

class HydraComm:
    def __init__(self, url: str, address_file: str, output_address_file: str, lovelace_value: int, threshold: int):
        self.url = url
        self.address_file = address_file
        self.output_address_file = output_address_file
        self.lovelace_value = lovelace_value
        self.threshold = threshold  # Set the threshold value here
        self.head_is_open_received = asyncio.Event()
        self.ready_to_fanout_received = asyncio.Event()

    async def listen(self):
        async with websockets.connect(self.url + "?history=no") as websocket:
            print("Connected to HydraComm")
            while True:
                message = await websocket.recv()
                await self.receive_message(message)

    async def receive_message(self, message: str):
        data = json.loads(message)
        if data.get("tag") == "HeadIsOpen":
            print("Received HeadIsOpen message:", data)
            self.head_is_open_received.set()  # Signal that the head is open
        elif data.get("tag") == "ReadyToFanout":
            print("Received ReadyToFanout message:", data)
            self.ready_to_fanout_received.set()  # Signal that we are ready to fanout
        else:
            print("Unexpected message:", data)

    async def send_message(self, message: str):
        async with websockets.connect(self.url + "?history=no") as websocket:
            await websocket.send(message)

    async def execute_command(self, command: str):
        """Executes a shell command and returns the output."""
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
                async with session.get("http://127.0.0.1:4001/snapshot/utxo") as response:
                    print(f"Response status: {response.status}")
                
                    # Read the response text directly
                    response_text = await response.text()
                
                    if response.status == 200:
                        try:
                            # Attempt to parse the response text as JSON
                            data = json.loads(response_text)
                        
                            # Your filtering logic here
                            filtered_utxo = {k: v for k, v in data.items() if v["address"] == self.get_address()}
                            if filtered_utxo:
                                lovelace_value = list(filtered_utxo.values())[0]['value']['lovelace']
                                print(f"Lovelace value: {lovelace_value}")
                                if lovelace_value >= self.threshold:
                                    break  # Exit the loop when threshold is met
                        except json.JSONDecodeError:
                            print("Failed to decode JSON response.")
                            print(f"Response text: {response_text}")
                    else:
                        print(f"Unexpected response status: {response.status}")
                        print(f"Response text: {response_text}")

            await asyncio.sleep(5)  # Adjust the sleep time as necessary

    def get_address(self):
        """Retrieve the address from the specified credentials file."""
        with open(self.address_file) as f:
            return f.read().strip()

    def get_output_address(self):
        """Retrieve the output address from the specified output address file."""
        with open(self.output_address_file) as f:
            return f.read().strip()

async def run_hydra_comm():
    url = "ws://127.0.0.1:4001"
    address_file = "credentials/alice-funds.addr"  # Change this as needed
    output_address_file = "credentials/bob-funds.addr"  # Change this as needed
    lovelace_value = 5000000  # Set your desired Lovelace value here
    threshold = 1000000  # Set your desired threshold value here
    hydra_comm = HydraComm(url, address_file, output_address_file, lovelace_value, threshold)

    # Start listening to the WebSocket in a separate task
    listener_task = asyncio.create_task(hydra_comm.listen())

    # Step 1: Send Init message
    #await hydra_comm.send_message('{"tag": "Init"}')
    utxo_command = (
        f"curl -s 127.0.0.1:4001/snapshot/utxo "
        f"| jq \"with_entries(select(.value.address == \\\"$(cat {address_file})\\\"))\" "
        f"> utxo.json"
    )
    await hydra_comm.execute_command(utxo_command)
    # Step 2: Wait for HeadIsOpen message
    await hydra_comm.head_is_open_received.wait()
    print(" Head is open")
    # Step 3a: Build the raw transaction
    build_command = (
        "cardano-cli conway transaction build-raw "
        f"--tx-in $(jq -r 'to_entries[0].key' < utxo.json) "
        f"--tx-out $(cat {output_address_file})+{hydra_comm.lovelace_value} "
        f"--tx-out $(cat {address_file})+$(jq 'to_entries[0].value.value.lovelace - {hydra_comm.lovelace_value}' < utxo.json) "
        "--fee 0 --out-file tx.json"
    )
    await hydra_comm.execute_command(build_command)

    # Step 3b: Sign the transaction
    sign_command = (
        "cardano-cli conway transaction sign "
        "--tx-body-file tx.json "
        f"--signing-key-file credentials/{address_file.split('/')[-1].replace('addr', 'sk')} "
        "--out-file tx-signed.json"
    )
    await hydra_comm.execute_command(sign_command)

    # Step 3c: Send the signed transaction
    with open("tx-signed.json") as f:
        signed_tx = f.read()
        await hydra_comm.send_message(json.dumps({"tag": "NewTx", "transaction": signed_tx}))
    print("Now Waiting for UTXO")
    # Step 4: Continuously check UTXO
    await hydra_comm.check_utxo()

    # Step 5: Send Close message
    await hydra_comm.send_message('{"tag": "Close"}')

    # Step 6: Wait for ReadyToFanout message
    await hydra_comm.ready_to_fanout_received.wait()
    print("Now Fanout for UTXO")
    # Step 7: Send Fanout message
    await hydra_comm.send_message('{"tag": "Fanout"}')

# To run the WebSocket client, use the following:
if __name__ == "__main__":
    asyncio.run(run_hydra_comm())
