---- MODULE EscrowCard ----
EXTENDS Naturals, TLC

(* Define constants *)
CONSTANTS
    TokenName \in ByteArray,
    PolicyId \in ByteArray,
    UTXOReference \in ByteArray,
    MintAmount \in Nat

(* Define state variables *)
VARIABLES
    inputs,               (* List of inputs *)
    minting,              (* Minting action *)
    balance               (* Token balance *)

(* Define initial state *)
Init == 
    /\ inputs = <<>>        (* Start with no inputs *)
    /\ minting = <<>>       (* No minting initially *)
    /\ balance = 0           (* Initial balance *)

(* Define actions *)
LockAction ==
    /\ \A input \in inputs: input.output_reference = UTXOReference
    /\ minting = <<(TokenName, 1)>>  (* Mint 1 token *)
    /\ balance' = balance + 1         (* Update balance *)
    /\ UNCHANGED <<inputs>>

RedeemAction ==
    /\ \A input \in inputs: input.output_reference = UTXOReference
    /\ minting = <<(TokenName, -1)>>  (* Redeem the token *)
    /\ balance' = balance - 1         (* Update balance *)
    /\ UNCHANGED <<inputs>>

(* Next state transition *)
Next ==
    \/ LockAction
    \/ RedeemAction

(* Define the specification *)
Spec == Init /\ [][Next]_<<inputs, minting, balance>>

(* Theorems to check *)
THEOREM Spec => []<>(balance >= 0)
======
