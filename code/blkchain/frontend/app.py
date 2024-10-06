from flask import Flask, request, jsonify, render_template
import asyncio
import json
import aiohttp
import sys
import os

# Adjust the path to import HydraClient from the code directory
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))
from hydra_client import HydraClient  # Adjusted import

app = Flask(__name__)

# Create a global instance of HydraClient
hydra_client = None

async def create_hydra_client(address_file, output_address_file, lovelace_value, threshold=1000000):
    global hydra_client
    hydra_client = HydraClient(address_file=address_file, output_address_file=output_address_file, lovelace_value=lovelace_value, threshold=threshold)
    await hydra_client.run()

@app.route('/')
def home():
    return render_template('index.html')

@app.route('/initialize', methods=['POST'])
async def initialize():
    data = request.form
    address_file = data.get('address_file')
    output_address_file = data.get('output_address_file')
    lovelace_value = int(data.get('lovelace_value'))

    if not (address_file and output_address_file and lovelace_value):
        return jsonify({"error": "Missing parameters"}), 400

    try:
        await create_hydra_client(address_file, output_address_file, lovelace_value)
        return jsonify({"status": "HydraClient initialized"}), 200
    except Exception as e:
        return jsonify({"error": str(e)}), 500

@app.route('/send_command', methods=['POST'])
async def send_command():
    data = request.form
    command = data.get('command')
    payload = data.get('payload', {})

    try:
        response = await hydra_client.handle_api_request(command, json.loads(payload))
        return jsonify(response)
    except Exception as e:
        return jsonify({"error": str(e)}), 400

if __name__ == '__main__':
    app.run(debug=True)
