Require Export wire.

Lemma shiftout_shiftin: forall A n (a: A) (v: t A n),
  shiftout (shiftin a v) = v.
Proof.
  intros. induction v; simpl; [reflexivity | rewrite IHv; reflexivity].
Qed.

Lemma last_shiftin: forall A n (a: A) (v: t A n),
  last (shiftin a v) = a.
Proof.
  intros. induction v; simpl; [reflexivity | rewrite IHv; reflexivity].
Qed.

Lemma hd_shiftin: forall A n (a: A) (v: t A (S n)),
  hd (shiftin a v) = hd v.
Proof. intros. rewrite (eta v). simpl. reflexivity. Qed.

Lemma tl_shiftin: forall A n (a: A) (v: t A (S n)),
  tl (shiftin a v) = shiftin a (tl v).
Proof. intros. rewrite (eta v). simpl. reflexivity. Qed.

