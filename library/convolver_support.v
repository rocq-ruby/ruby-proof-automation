Require Export twod.
Require Import ZArith.
Require Import Lia.

(* ================================================================= *)
(* Part 1: generic auxiliary lemmas                                   *)
(* ================================================================= *)

(* Powers commute with FST. *)
Lemma pow_fst:
  forall (A C : Type) (R : rel A A) (n : nat),
  (FST (C:=C) R) ^^ n = FST (R ^^ n).
Proof.
  intros A C R n. induction n.
  - simpl. unfold FST. now rewrite para_id.
  - simpl. rewrite IHn, fst_series. reflexivity.
Qed.

(* Every vector of positive length is a snoc. *)
Lemma snoc_inv:
  forall (A : Type) (p : nat) (u : t A (S p)),
  exists b v, u = shiftin b v.
Proof.
  intros. exists (last u), (shiftout u).
  apply vec_shiftin_last_shiftout.
Qed.

(* The snoc-recursion of the triangle, pointwise. *)
Lemma tri_snoc:
  forall (A : Type) (p : nat) (R : rel A A) (b c : A) (v w : t A p),
  tri (S p) R (shiftin b v) (shiftin c w) <-> tri p R v w /\ (R ^^ p) b c.
Proof.
  intros. simpl. split.
  - intros [k2 [k1 H1 H2] H3].
    destruct k1 as [f0 l0]. destruct k2 as [f1 l1].
    unfold converse, apr in H1. simpl in H1.
    apply vec_shiftin_eq in H1. destruct H1 as [Hl0 Hf0].
    unfold parallel in H2. simpl in H2. destruct H2 as [Ht Hp].
    unfold apr in H3. simpl in H3.
    apply vec_shiftin_eq in H3. destruct H3 as [Hl1 Hf1].
    subst. auto.
  - intros [Ht Hp].
    exists (w, c).
    + exists (v, b).
      * unfold converse, apr. reflexivity.
      * unfold parallel. simpl. auto.
    + unfold apr. reflexivity.
Qed.

(* Consequences of the two delay cancellations. *)
Lemma cancel_total:
  forall (A : Type) (R : rel A A),
  R; R^~1 = id A ->
  forall a : A, exists b : A, R a b.
Proof.
  intros A R H a.
  assert (Hc: (R; R^~1) a a) by (rewrite H; reflexivity).
  destruct Hc as [b Hb _]. exists b. exact Hb.
Qed.

Lemma cancel_func:
  forall (A : Type) (R : rel A A),
  R^~1; R = id A ->
  forall k a b : A, R k a -> R k b -> a = b.
Proof.
  intros A R H k a b Ha Hb.
  assert (Hc: (R^~1; R) a b) by (exists k; assumption).
  rewrite H in Hc. exact Hc.
Qed.

Lemma pow_func:
  forall (A : Type) (R : rel A A),
  (forall k a b : A, R k a -> R k b -> a = b) ->
  forall (n : nat) (k a b : A), (R^^n) k a -> (R^^n) k b -> a = b.
Proof.
  intros A R HF n. induction n; intros k a b Ha Hb.
  - simpl in Ha, Hb. unfold id in Ha, Hb. congruence.
  - simpl in Ha, Hb.
    destruct Ha as [a' Ha1 Ha2]. destruct Hb as [b' Hb1 Hb2].
    assert (a' = b') by (eapply IHn; eauto). subst.
    eapply HF; eauto.
Qed.

(* ================================================================= *)
(* Part 2: the data loader (contour step)                             *)
(*                                                                    *)
(* dstl n; tri n (FST D)  =  row n (fork; SND (pi1; D)); pi1          *)
(*                                                                    *)
(* Drawing the contour lines along the distributor row moves one      *)
(* delay into each cell; the anti-delays cancel the triangular array  *)
(* entirely, so no boundary terms remain.                             *)
(* ================================================================= *)

(* Pointwise reading of the distributor cell. *)
Lemma dist_cell_pt:
  forall (A B : Type) (x : A) (w : B) (pr : A * B) (g : A),
  (fork; SND pi1) (x, w) (pr, g) <-> pr = (x, w) /\ g = x.
Proof.
  intros. split.
  - intros [[k1 k2] HF HS].
    simpl in HF. destruct HF as [E1 E2].
    destruct HS as [E3 E4]. unfold pi1, id in *. simpl in *.
    subst. auto.
  - intros [-> ->]. exists ((x, w), (x, w)).
    + simpl. auto.
    + split; unfold pi1, id; reflexivity.
Qed.

(* Pointwise reading of the pipelined distributor cell. *)
Lemma dist_cellD_pt:
  forall (A B : Type) (E : rel A A) (x : A) (w : B) (pr : A * B) (g : A),
  (fork; SND (pi1; E)) (x, w) (pr, g) <-> pr = (x, w) /\ E x g.
Proof.
  intros. split.
  - intros [[k1 k2] HF HS].
    simpl in HF. destruct HF as [E1 E2].
    destruct HS as [E3 [m Hm HE]]. unfold pi1, id in *. simpl in *.
    subst. auto.
  - intros [-> HE]. exists ((x, w), (x, w)).
    + simpl. auto.
    + split.
      * unfold id. reflexivity.
      * exists x. unfold pi1. reflexivity. exact HE.
Qed.

(* The distributor row threads its horizontal input unchanged. *)
Lemma dist_row_thread:
  forall (A B : Type) (p : nat) (x g : A) (v : t B p) (f : t (A * B) p),
  row_pw p (fork; SND pi1) (x, v) (f, g) -> g = x.
Proof.
  intros A B p. induction p; intros x g v f H.
  - simpl in H. unfold row_zero in H. simpl in H. auto.
  - simpl in H. destruct H as [g0 Hc Hrest].
    apply dist_cell_pt in Hc. destruct Hc as [_ ->].
    eapply IHp. exact Hrest.
Qed.

(* The pipelined distributor row delays its input p times end to end. *)
Lemma chainD_pow:
  forall (A B : Type) (E : rel A A) (p : nat)
  (x g : A) (v : t B p) (f : t (A * B) p),
  row_pw p (fork; SND (pi1; E)) (x, v) (f, g) -> (E ^^ p) x g.
Proof.
  intros A B E p. induction p; intros x g v f H.
  - simpl in H. unfold row_zero in H. simpl in H. subst. reflexivity.
  - simpl in H. destruct H as [g0 Hc Hrest].
    apply dist_cellD_pt in Hc. destruct Hc as [_ HE].
    rewrite <- pow_left. exists g0. exact HE.
    eapply IHp. exact Hrest.
Qed.

Lemma vec_eta:
  forall (A : Type) (p : nat) (v : t A (S p)),
  v = hd v :: tl v.
Proof.
  intros A p v. apply (caseS' v). intros. reflexivity.
Qed.

(* Pointwise left-reduction. *)
Fixpoint rdl_pw {A B : Type} (n : nat) (Q : rel (A * B) A) : rel (A * t B n) A :=
  match n with
  | 0 => rdl_zero
  | S p => fun '(a, v) y =>
      exists2 a', Q (a, hd v) a' & rdl_pw p Q (a', tl v) y
  end.

Lemma rdl_dual:
  forall (A B : Type) (n : nat) (Q : rel (A * B) A),
  rdl n Q = rdl_pw n Q.
Proof.
  intros A B n Q. induction n; [reflexivity|].
  simpl. rewrite IHn.
  rel_ext.
  - destruct x as [a v].
    intros [k3 [k2 [k1 H1 H2] H3] H4].
    destruct k1 as [a1 [h tv]].
    unfold converse, SND, parallel, apl, id in H1. simpl in H1.
    destruct H1 as [Ha1 Hv].
    destruct k2 as [[a2 h2] t2].
    unfold rsh in H2. simpl in H2.
    destruct H2 as [Ha2 [Hh2 Ht2]].
    destruct k3 as [a3 t3].
    unfold FST, parallel, id in H3. simpl in H3.
    destruct H3 as [HQ Ht3].
    subst. simpl.
    exists a3.
    + exact HQ.
    + exact H4.
  - destruct x as [a v].
    intros H. simpl in H. destruct H as [a' HQ Hr].
    exists (a', tl v).
    + exists ((a, hd v), tl v).
      * exists (a, (hd v, tl v)).
        -- unfold converse, SND, parallel, apl, id. simpl. split.
           ++ reflexivity.
           ++ symmetry. apply vec_eta.
        -- unfold rsh. simpl. split; [reflexivity | split; reflexivity].
      * unfold FST, parallel, id. simpl. split.
        -- exact HQ.
        -- reflexivity.
    + exact Hr.
Qed.

(* The row/reduction fusion, pointwise. *)
Lemma fuse_pw:
  forall (X W P Acc J : Type)
  (S : rel (X * W) (P * X)) (Q : rel (Acc * P) Acc) (j : J)
  (n : nat) (a : Acc) (x : X) (ws : t W n) (y : Acc),
  (exists ps xo, row_pw n S (x, ws) (ps, xo) /\ rdl_pw n Q (a, ps) y)
  <->
  (exists js acc xo,
     row_pw n (below_pw (Q; (pi2 (A:=J))^~1) S) ((a, x), ws) (js, (acc, xo)) /\
     acc = y).
Proof.
  intros X W P Acc J S Q j n. induction n; intros a x ws y.
  - split.
    + intros (ps & xo & Hrow & Hrdl).
      simpl in Hrow. unfold row_zero in Hrow. simpl in Hrow.
      simpl in Hrdl. unfold rdl_zero in Hrdl. simpl in Hrdl.
      exists (nil J), a, x. split.
      * simpl. unfold row_zero. reflexivity.
      * exact Hrdl.
    + intros (js & acc & xo & Hrow & Hy).
      simpl in Hrow. unfold row_zero in Hrow. simpl in Hrow.
      injection Hrow as Ha Hx. subst acc. subst xo.
      exists (nil P), x. split.
      * simpl. unfold row_zero. reflexivity.
      * simpl. unfold rdl_zero. simpl. exact Hy.
  - split.
    + intros (ps & xo & Hrow & Hrdl).
      simpl in Hrow. destruct Hrow as [g Hcell Hrest].
      simpl in Hrdl. destruct Hrdl as [a' HQ Hrdl'].
      assert (HR: exists js acc xo',
        row_pw n (below_pw (Q; (pi2 (A:=J))^~1) S) ((a', g), tl ws) (js, (acc, xo')) /\
        acc = y).
      { apply (proj1 (IHn a' g (tl ws) y)). exists (tl ps), xo. split; assumption. }
      destruct HR as (js & acc & xo' & Hrow' & Hacc).
      exists (j :: js), acc, xo'. split; [| exact Hacc].
      simpl. exists (a', g).
      * exists (hd ps).
        -- exists a'.
           ++ exact HQ.
           ++ unfold converse, pi2. reflexivity.
        -- exact Hcell.
      * exact Hrow'.
    + intros (js & acc & xo & Hrow & Hacc).
      simpl in Hrow. destruct Hrow as [g' Hc Hrest].
      destruct g' as [a' g].
      simpl in Hc. destruct Hc as [gg HQpi HS].
      destruct HQpi as [m HQ Hpi].
      unfold converse, pi2 in Hpi. simpl in Hpi. subst m.
      assert (HL: exists ps xo',
        row_pw n S (g, tl ws) (ps, xo') /\ rdl_pw n Q (a', ps) y).
      { apply (proj2 (IHn a' g (tl ws) y)). exists (tl js), acc, xo. split; assumption. }
      destruct HL as (ps' & xo' & Hrow'' & Hrdl'').
      exists (gg :: ps'), xo'. split.
      * simpl. exists g.
        -- exact HS.
        -- exact Hrow''.
      * simpl. exists a'.
        -- exact HQ.
        -- exact Hrdl''.
Qed.

(* The fusion, structurally. *)
Lemma row_rdl_below:
  forall (X W P Acc J : Type)
  (S : rel (X * W) (P * X)) (Q : rel (Acc * P) Acc) (j : J) (n : nat),
  lsh; SND (row n S; pi1); rdl n Q
  = row n ((Q; (pi2 (A:=J))^~1) <||> S); pi2; pi1.
Proof.
  intros X W P Acc J S Q j n.
  rewrite below_dual, !row_dual, rdl_dual.
  rel_ext.
  - destruct x as [[a x1] ws].
    intros [k2 [k1 H1 H2] H3].
    destruct k1 as [a1 [x2 ws1]].
    unfold lsh in H1. simpl in H1.
    destruct H1 as [Ha1 [Hx2 Hws1]].
    destruct k2 as [a2 ps].
    destruct H2 as [Ha2 Hrp].
    unfold id in Ha2. simpl in Ha2.
    destruct Hrp as [pxo Hrow Hpi].
    destruct pxo as [ps0 xo].
    unfold pi1 in Hpi. simpl in Hpi.
    subst a1 x2 ws1 a2 ps.
    assert (HF: exists js acc xo',
      row_pw n (below_pw (Q; (pi2 (A:=J))^~1) S) ((a, x1), ws) (js, (acc, xo')) /\
      acc = x0).
    { apply (proj1 (fuse_pw X W P Acc J S Q j n a x1 ws x0)).
      exists ps0, xo. split; assumption. }
    destruct HF as (js & acc & xo' & Hrow' & Hacc).
    exists (acc, xo').
    + exists (js, (acc, xo')).
      * exact Hrow'.
      * unfold pi2. reflexivity.
    + exact Hacc.
  - destruct x as [[a x1] ws].
    intros [k2 [k1 Hrow H2] H3].
    destruct k1 as [js axo].
    unfold pi2 in H2. simpl in H2. subst k2.
    destruct axo as [acc xo].
    unfold pi1 in H3. simpl in H3.
    assert (HL: exists ps xo',
      row_pw n S (x1, ws) (ps, xo') /\ rdl_pw n Q (a, ps) x0).
    { apply (proj2 (fuse_pw X W P Acc J S Q j n a x1 ws x0)).
      exists js, acc, xo. split; assumption. }
    destruct HL as (ps & xo' & Hrow'' & Hrdl'').
    exists (a, ps).
    + exists (a, (x1, ws)).
      * unfold lsh. simpl. split; [reflexivity | split; reflexivity].
      * split.
        -- unfold id. reflexivity.
        -- exists (ps, xo').
           ++ exact Hrow''.
           ++ unfold pi1. reflexivity.
    + exact Hrdl''.
Qed.

Definition mac : rel (nat * (nat * nat)) nat :=
  fun i j => fst i + fst (snd i) * snd (snd i) = j.


Section Convolver.

(* The delay primitive.  Its two cancellation laws are imported as
   hypotheses by Cu0_Cu1 and discharged for the stream model below. *)
Variable D : forall A : Type, rel A A.

(* One cell of the regular design: a mac above a pipelined distributor.
   The type ascription pins the phantom bottom output of pi2^~1 to nat. *)
Definition CuCell1 : rel ((nat * nat) * nat) (nat * (nat * nat)) :=
  (mac; pi2^~1) <||> (fork; SND (pi1; D nat)).

(* The reference design: distribute x, delay the i-th tap i times,
   then reduce with mac from the left. *)
Definition Cu0 (n : nat) : rel ((nat * nat) * t nat n) nat :=
  lsh; SND (dstl n; tri n (FST (D nat))); rdl n mac.

(* The regular design: a row of identical cells. *)
Definition Cu1 (n : nat) : rel ((nat * nat) * t nat n) nat :=
  row n CuCell1; pi2; pi1.


End Convolver.
