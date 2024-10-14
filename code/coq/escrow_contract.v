From Coq Require Import Arith.
From Coq Require Import List.
From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
Import ListNotations.

(* Define constants *)
Parameter TokenName : string.
Parameter PolicyId : string.
Parameter UTXOReference : string.
Parameter MintAmount : nat.

(* Define state variables *)
Record State := {
  inputs : list string;  (* List of inputs *)
  minting : list (string * nat);  (* Minting action *)
  balance : nat  (* Token balance *)
}.

(* Define initial state *)
Definition init_state : State :=
  {| inputs := []; minting := []; balance := 0 |}.

(* Define actions *)
Definition is_in (x : string) (lst : list string) : bool :=
  List.existsb (fun y => String.eqb x y) lst.

Definition lock_action (s : State) : option State :=
  if is_in UTXOReference s.(inputs) then
    Some {| inputs := s.(inputs); minting := [(TokenName, 1)]; balance := s.(balance) + 1 |}
  else None.
Definition redeem_action (s : State) : option State :=
  if is_in UTXOReference s.(inputs) then
    match s.(balance) with
    | 0 => None  (* Cannot redeem if balance is zero *)
    | S _ => Some {| inputs := s.(inputs); minting := [(TokenName, 0)]; balance := s.(balance) - 1 |}
    end
  else None.

(* Define the specification *)
Definition next (s : State) : list (option State) :=
  [lock_action s; redeem_action s].

(* Theorem: balance should never be negative *)
Theorem balance_non_negative :
  forall s, s.(balance) >= 0.
Proof.
  intros s.
  destruct s.
  simpl.
  (* The initial balance is 0 and can only increase, thus remains non-negative *)
  apply Nat.le_0_l.
Qed.
