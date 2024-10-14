# Escrow Contract in Coq

## Overview

This repository contains a formal specification and proof of an escrow contract written in Coq. The contract allows a party to send funds to an escrow and receive a non-fungible token (NFT) as a receipt. When the party submits the receipt, they can redeem their funds.

## Features

- Formal specification of the escrow contract.
- Proofs of important properties, such as balance non-negativity.
- Clear structure for state management and actions.

## Getting Started

### Prerequisites

To work with this project, ensure you have the following installed:

- [Coq](https://coq.inria.fr/) (version 8.18 or higher)
- [OPAM](https://opam.ocaml.org/) (optional, for managing OCaml and Coq dependencies)

### Usage
```
coqc escrow_contract.v
```

You can interact with the Coq environment using coqtop:

```
coqtop

```

### Usage with COQIDE


1. Open CoqIDE: Launch CoqIDE from your terminal or applications menu.
2. Load the Project: Use the "File" menu to open the escrow.v file.
3. Navigate and Interact:
     1. You can step through the code, check types, and run proofs interactively.
     2. Use the "Step" button to process each command or use the keyboard shortcuts for navigation.
     3. Compiling: CoqIDE will automatically compile your changes as you work. You can see any errors in the output window.
     4. Running Proofs: You can execute your proofs by highlighting the relevant lines and clicking "Run" or using the shortcut.



