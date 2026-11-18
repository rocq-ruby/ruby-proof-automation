Require Export rows.

Lemma row_pw_equiv:
  forall A B C (n:nat) (R: rel (A*B) (C*A)),
  row_pw n R = row_pw2 n R.
Proof.
  intros. induction n; [reflexivity|].
  extensionality i; destruct i as [a v].
  extensionality j; destruct j as [w a_out].
  apply propositional_extensionality.
  simpl row_pw2. fold (@row_pw2 A B C). rewrite <- IHn.
  split.
  + intro H. apply row_pw_snoc.
    rewrite <- (vec_shiftin_last_shiftout _ _ v).
    rewrite <- (vec_shiftin_last_shiftout _ _ w). exact H.
  + intro H.
    rewrite (vec_shiftin_last_shiftout _ _ v).
    rewrite (vec_shiftin_last_shiftout _ _ w).
    apply row_pw_snoc. exact H.
Qed.

Lemma row2_dual:
  forall A B C (n:nat) (R: rel (A*B) (C*A)),
  row2 n R = row_pw n R.
Proof. intros. rewrite row_pw_equiv. apply row2_dual2. Qed.

Lemma row_row2:
  forall A B C (n:nat) (R: rel (A*B) (C*A)),
  row n R = row2 n R.
Proof. intros. rewrite row_dual, row2_dual. reflexivity. Qed.

(* ================================================================= *)
(*  Col: definitions                                                  *)
(* ================================================================= *)

Definition col_zero {A B C}:
  rel (t A 0*B) (B*t C 0) :=
  fun i j => snd i = fst j.

Fixpoint col {A B C} 
  (n:nat) (R: rel (A*B) (B*C)) :=
  match n with
    0 => col_zero
  | S p => FST ((apl p)^~1); R <||> (col p R); SND (apl p)
  end.

Fixpoint col2 {A B C} 
  (n:nat) (R: rel (A*B) (B*C)) :=
  match n with
    0 => col_zero
  | S p => FST ((apr p)^~1); (col2 p R) <||> R; SND(apr p)
  end.
  
Fixpoint col_pw {A B C} (n:nat) (R: rel (A*B) (B*C)):
  rel (t A n * B) (B * t C n) :=
  match n with
  | 0 => col_zero
  | S p => fun '(v, b) '(b_out, w) =>
      exists2 g, R (hd v, g) (b_out, hd w) &
        col_pw p R (tl v, b) (g, tl w)
  end.

Fixpoint col_pw2 {A B C} (n:nat) (R: rel (A*B) (B*C)):
  rel (t A n * B) (B * t C n) :=
  match n with
  | 0 => col_zero
  | S p => fun '(v, b) '(b_out, w) =>
      exists2 g, R (last v, b) (g, last w) &
        col_pw2 p R (shiftout v, g) (b_out, shiftout w)
  end.

(* ================================================================= *)
(*  Col: duality proofs                                               *)
(* ================================================================= *)

Lemma col_dual:
  forall A B C (n:nat) (R: rel (A*B) (B*C)),
  col n R = col_pw n R.
Proof.
  intros. induction n; [reflexivity|].
  simpl. rewrite IHn, below_dual. unfold_pw.
  rel_ext; destruct x as [v b]; destruct x0 as [b_out w]; simpl.
  + dual_fwd_apl.
  + intros [g HR Hcol].
    exists (b_out, (hd w, tl w)). exists ((hd v, tl v), b).
    * simpl. split; [symmetry; apply eta | reflexivity].
    * simpl. exists g; assumption.
    * simpl. split; [reflexivity | symmetry; apply eta].
Qed.

Lemma col2_dual2:
  forall A B C (n:nat) (R: rel (A*B) (B*C)),
  col2 n R = col_pw2 n R.
Proof.
  intros. induction n; [reflexivity|].
  simpl. rewrite IHn, below_dual. unfold_pw.
  rel_ext; destruct x as [v b]; destruct x0 as [b_out w]; simpl.
  + dual_fwd_apr.
  + intros [g HR Hcol].
    exists (b_out, (shiftout w, last w)). exists ((shiftout v, last v), b).
    * simpl. split; [symmetry; apply vec_shiftin_last_shiftout | reflexivity].
    * simpl. exists g; assumption.
    * simpl. split; [reflexivity | symmetry; apply vec_shiftin_last_shiftout].
Qed.

Lemma col_pw_snoc:
  forall A B C (n:nat) (R: rel (A*B) (B*C))
  (b b_out: B) (v: t A n) (a: A) (w: t C n) (c: C),
  col_pw (S n) R (shiftin a v, b) (b_out, shiftin c w) <->
  exists2 g, R (a, b) (g, c) & col_pw n R (v, g) (b_out, w).
Proof.
  intros A B C n. induction n; intros.
  - rewrite (nil_spec v), (nil_spec w). simpl. split.
    + intros [g HR Hz]. unfold col_zero in Hz. simpl in Hz. subst.
      exists b_out. exact HR. unfold col_zero; simpl; reflexivity.
    + intros [g HR Hz]. unfold col_zero in Hz. simpl in Hz. subst.
      exists b. exact HR. unfold col_zero; simpl; reflexivity.
  - rewrite (eta v), (eta w). simpl shiftin.
    simpl col_pw at 1. fold (@col_pw A B C).
    split.
    + intros [g1 HR1 Hrest].
      apply IHn in Hrest. destruct Hrest as [g2 HR2 Hcol].
      exists g2; [exact HR2 | simpl; exists g1; assumption].
    + intros [g2 HR2 Hcol].
      simpl in Hcol. destruct Hcol as [g1 HR1 Hcol'].
      exists g1. exact HR1. apply IHn. exists g2; assumption.
Qed.

Lemma col_pw_equiv:
  forall A B C (n:nat) (R: rel (A*B) (B*C)),
  col_pw n R = col_pw2 n R.
Proof.
  intros. induction n; [reflexivity|].
  extensionality i; destruct i as [v b].
  extensionality j; destruct j as [b_out w].
  apply propositional_extensionality.
  simpl col_pw2. fold (@col_pw2 A B C). rewrite <- IHn.
  split.
  + intro H.
    rewrite (vec_shiftin_last_shiftout _ _ v) in H.
    rewrite (vec_shiftin_last_shiftout _ _ w) in H.
    apply col_pw_snoc. exact H.
  + intro H.
    rewrite (vec_shiftin_last_shiftout _ _ v).
    rewrite (vec_shiftin_last_shiftout _ _ w).
    apply col_pw_snoc. exact H.
Qed.

Lemma col2_dual:
  forall A B C (n:nat) (R: rel (A*B) (B*C)),
  col2 n R = col_pw n R.
Proof. intros. rewrite col_pw_equiv. apply col2_dual2. Qed.

Lemma col_col2:
  forall A B C (n:nat) (R: rel (A*B) (B*C)),
  col n R = col2 n R.
Proof. intros. rewrite col_dual, col2_dual. reflexivity. Qed.

(* ================================================================= *)
(*  Misc definitions                                                  *)
(* ================================================================= *)

Definition dstl {A B} (n:nat):=
  row n (fork(A:=A*B); SND pi1); pi1.

Definition dstr {A B} (n:nat):=
  col n (fork(A:=A*B); FST pi2); pi2.

(* ================================================================= *)
(*  Mapn: pointwise spec                                              *)
(* ================================================================= *)

Fixpoint mapn_pw {A B} (n:nat) (R: rel A B): rel (t A n) (t B n) :=
  match n with
  | 0 => mapn_zero
  | S p => fun va wb => R (hd va) (hd wb) /\ mapn_pw p R (tl va) (tl wb)
  end.

Fixpoint mapn_pw2 {A B} (n:nat) (R: rel A B): rel (t A n) (t B n) :=
  match n with
  | 0 => mapn_zero
  | S p => fun va wb => 
      R (last va) (last wb) /\ mapn_pw2 p R (shiftout va) (shiftout wb)
  end.

Lemma mapn_dual2:
  forall A B (n:nat) (R: rel A B),
  mapn n R = mapn_pw2 n R.
Proof.
  intros. induction n; [reflexivity|].
  simpl. rewrite IHn. unfold series, converse, parallel, apr.
  rel_ext.
  + intros [k [k0 Hv [Hmap HR]] Hw].
    destruct k0 as [as0 a0]. destruct k as [bs0 b0]. simpl in *.
    subst. rewrite !shiftout_shiftin, !last_shiftin. auto.
  + intros [HR Hmap].
    exists (shiftout x0, last x0). exists (shiftout x, last x). simpl.
    * symmetry. apply vec_shiftin_last_shiftout.
    * split; [exact Hmap | exact HR].
    * symmetry. apply vec_shiftin_last_shiftout.
Qed.

Lemma mapn_pw_snoc:
  forall A B (n:nat) (R: rel A B) (a: A) (b: B) (va: t A n) (wb: t B n),
  mapn_pw (S n) R (shiftin a va) (shiftin b wb) <->
  R a b /\ mapn_pw n R va wb.
Proof.
  intros A B n. induction n; intros.
  - rewrite (nil_spec va), (nil_spec wb). simpl. tauto.
  - change (R (hd (shiftin a va)) (hd (shiftin b wb)) /\
            mapn_pw (S n) R (tl (shiftin a va)) (tl (shiftin b wb)) <->
            R a b /\ mapn_pw (S n) R va wb).
    rewrite !hd_shiftin, !tl_shiftin. rewrite IHn.
    change (mapn_pw (S n) R va wb) with 
           (R (hd va) (hd wb) /\ mapn_pw n R (tl va) (tl wb)).
    tauto.
Qed.

Lemma mapn_pw_equiv:
  forall A B (n:nat) (R: rel A B),
  mapn_pw n R = mapn_pw2 n R.
Proof.
  intros. induction n; [reflexivity|].
  extensionality va. extensionality wb.
  apply propositional_extensionality.
  simpl mapn_pw2. fold (@mapn_pw2 A B). rewrite <- IHn.
  split.
  + intro H.
    rewrite (vec_shiftin_last_shiftout _ _ va) in H.
    rewrite (vec_shiftin_last_shiftout _ _ wb) in H.
    exact (proj1 (mapn_pw_snoc _ _ _ _ _ _ _ _) H).
  + intro H.
    rewrite (vec_shiftin_last_shiftout _ _ va).
    rewrite (vec_shiftin_last_shiftout _ _ wb).
    exact (proj2 (mapn_pw_snoc _ _ _ _ _ _ _ _) H).
Qed.

Lemma mapn_dual:
  forall A B (n:nat) (R: rel A B),
  mapn n R = mapn_pw n R.
Proof. intros. rewrite mapn_pw_equiv. apply mapn_dual2. Qed.

(* ================================================================= *)
(*  col_snd_mapn: absorbing mapn into col                             *)
(* ================================================================= *)

Lemma col_pw_snd_mapn_pw:
  forall A B C (n:nat) (R: rel (A*B) (B*A)) (S: rel A C)
    va b b_out wc,
  (exists wa, col_pw n R (va, b) (b_out, wa) /\ mapn_pw n S wa wc)
  <-> col_pw n (R; SND S) (va, b) (b_out, wc).
Proof.
  intros A B C n. induction n; intros.
  - simpl. unfold col_zero, mapn_zero. split.
    + intros [wa [Hb [Hwa Hwc]]]. subst. simpl in Hb. simpl. apply Hb.
    + intro Hb. exists (nil A). 
      rewrite (empty_is_nil C (a:=wc)).
      split; [exact Hb | split; reflexivity].
  - simpl. split.
    + intros [wa [[g HR Hcol] [HS Hmapn]]].
      exists g.
      * unfold series, SND, parallel, id. exists (b_out, hd wa).
        exact HR. simpl; auto.
      * apply IHn. exists (tl wa). auto.
    + intros [g [k HR Hstep] Hcol].
      unfold SND, parallel, id in Hstep. destruct k as [b' a']. simpl in Hstep.
      destruct Hstep as [<- HS].
      apply IHn in Hcol. destruct Hcol as [wa [Hcol Hmapn]].
      exists (a' :: wa). split.
      * exists g. exact HR. exact Hcol.
      * simpl. auto.
Qed.

Lemma col_snd_mapn:
  forall A B C (n:nat) (R: rel (A*B) (B*A)) (S: rel A C),
  col n R; SND (mapn n S) = col n (R; SND S).
Proof.
  intros. rewrite !col_dual, mapn_dual.
  unfold series, SND, parallel, id.
  rel_ext; destruct x as [va b]; destruct x0 as [b_out wc]; simpl.
  - intros [k Hcol [<- Hmapn]].
    destruct k as [b_out' wa]. simpl in *.
    apply col_pw_snd_mapn_pw. exists wa. auto.
  - intro H. apply col_pw_snd_mapn_pw in H.
    destruct H as [wa [Hcol Hmapn]].
    exists (b_out, wa). exact Hcol. simpl; auto.
Qed.

(* ================================================================= *)
(*  Grid: row of columns                                             *)
(* ================================================================= *)

Definition grid {A B} 
  (m:nat) (n:nat) (R: rel (A*B) (B*A)):=
  row m (col n R).

