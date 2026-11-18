Require Import convolver_support.

Lemma Cu0_Cu1: forall (D : forall A : Type, rel A A) (n : nat),
  D nat; (D nat)^~1 = id nat /\ (D nat)^~1; D nat = id nat ->
  @Cu0 D n = @Cu1 D n.
Proof.
(* Open obligation; no solution supplied. *)
