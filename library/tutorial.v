Require Import rec loop rows.

(* Small executable examples accompanying TUTORIAL.md. *)
Definition ADDER : rel (nat * nat) nat :=
  fun input output => fst input + snd input = output.

Example add_two_three : ADDER (2, 3) 5.
Proof. reflexivity. Qed.

Example duplicate_then_add : (fork; ADDER) 4 8.
Proof.
  exists (4, 4).
  - split; reflexivity.
  - reflexivity.
Qed.

Example append_value : (apr 0) (nil nat, 3) (cons nat 3 0 (nil nat)).
Proof. reflexivity. Qed.

Example empty_reduction : rdl 0 ADDER (7, nil nat) 7.
Proof. reflexivity. Qed.

Example regroup_ports :
  @lsh nat nat nat; rsh = id ((nat * nat) * nat).
Proof. apply lsh_rsh. Qed.
