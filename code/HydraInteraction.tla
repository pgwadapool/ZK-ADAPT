---- MODULE HydraInteraction ----
EXTENDS Naturals, Sequences

CONSTANTS Parties, HydraHeadURL

VARIABLES websocketState, hydraHeadState, messages, transactions


(* --define the initial state of the system-- *)
Init ==
    /\ websocketState = [party \in Parties |-> "disconnected"]
    /\ hydraHeadState = "closed"
    /\ messages = << >>
    /\ transactions = {}  \* Initializing as an empty set



(* --define the state transitions-- *)
OpenHydraHead ==
    /\ hydraHeadState = "closed"
    /\ hydraHeadState' = "open"
    /\ transactions' = transactions
    /\ websocketState' = [party \in Parties |-> "connected"]
    /\ messages' = Append(messages, "Hydra head opened")

SendTransaction(party) ==
    /\ websocketState[party] = "connected"
    /\ hydraHeadState = "open"
    /\ transactions' = transactions \cup {party}  \* Add the party to the set of transactions
    /\ websocketState' = websocketState  \* State unchanged
    /\ hydraHeadState' = hydraHeadState  \* State unchanged
    /\ messages' = messages  \* State unchanged

CloseHydraHead ==
    /\ hydraHeadState = "open"
    /\ hydraHeadState' = "closed"
    /\ transactions' = transactions  \* State unchanged
    /\ websocketState' = websocketState  \* State unchanged
    /\ messages' = Append(messages, "Hydra head closed")

(* --define the model behavior-- *)
Next ==
    \/ \E party \in Parties: SendTransaction(party)
    \/ OpenHydraHead
    \/ CloseHydraHead

(* --define the specification-- *)
Spec ==
    /\ Init
    /\ [][Next]_<<websocketState, hydraHeadState, transactions,messages>>

=================================
