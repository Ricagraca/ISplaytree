Set Implicit Arguments.
From TLC Require Import LibTactics LibLogic LibProd LibEpsilon LibContainer
     LibSet LibRelation LibPer LibMonoid.
Local Notation path := rtclosure.
From iris_time.union_find.math Require Import LibNatExtra LibIter LibRewrite
     InverseNatNat Ackermann InverseAckermann MiscArith TLCBuffer
     UnionFind01Data UnionFind11Rank UnionFind21Parent.

(* Following Tarjan's course notes and Cormen-Leiserson-Rivest, we now define
   the level [k], the index [i], and the potential functions [phi] and [Phi]. *)

(* -------------------------------------------------------------------------- *)

Section Tarjan.

(* In the following, we again assume that [F] is a ranked disjoint set forest
   with domain [D] and ranks [K]. *)

Variable V : Type.
Variable D : set V.
Variable F : binary V.
Variable K : V -> nat.
Hypothesis is_rdsf_F:
  is_rdsf D F K.

Notation p := (p F).

(* -------------------------------------------------------------------------- *)

Section NonRoot.

(* Let [x] be a non-root. *)

Variable x : V.
Hypothesis x_non_root: ~ is_root F x.

(* -------------------------------------------------------------------------- *)

(* Assume the rank of [x] is at least 1. *)

Hypothesis x_has_nonzero_rank:
  0 < K x.

(* The level of [x] is defined as the largest [k] such that
   [A k (K x)] is less than or equal to [K (p x)]. *)

Definition k :=
  betaf (fun k => A k (K x)) (K (p x)).

(* The following lemma proves that [k] is well-defined. *)

Lemma k_exists:
  A 0 (K x) <= K (p x).
Proof using is_rdsf_F x_non_root.
  rewrite Abase_eq. eapply parent_has_greater_rank; eauto.
Qed.

Ltac k th :=
  eapply th with (f := fun k => A k (K x));
  eauto using k_exists with monotonic.

(* The level of [x] seems to be a measure of the distance of the rank
   of [x] and the rank of its parent. In the case where these ranks
   are closest, [K (p x)] is [K x + 1], so [k] is 0. *)

Lemma k_is_zero:
  K (p x) = K x + 1 ->
  k = 0.
Proof using x_has_nonzero_rank.
  introv h. unfold k. rewrite h. eapply beta_x_succ_x. eauto.
Qed.

(* In the case where these ranks are furthest away, [K x] is 1
   and [K (p x)] is, say, [n - 1]. (In reality, ranks are bounded
   by [log2 n], but we don't need this information here.) This
   shows that [k] is less than [alpha n]. *)

Lemma k_lt_alpha:
  forall n,
  card D <= n ->
  k < alpha n.
Proof using is_rdsf_F x_non_root x_has_nonzero_rank.
  intros.
  (* By definition of [k], it suffices to prove [K (p x) < A (alpha n) (K x)]. *)
  k betaf_spec_direct_contrapositive.
  (* Because [K x] is greater than zero, it suffices to consider the worst
     case where [K x] is 1. *)
  eapply Nat.lt_le_trans with (m := A (alpha n) 1); [ |
    eauto with monotonic lia ].
  (* By definition of [alpha], [A (alpha n) 1] is at most [n]. *)
  eapply Nat.lt_le_trans with (m := n); [ |
    alpha f_alphaf ].
  (* There remains to argue that every rank is less than [n]. *)
  eapply Nat.lt_le_trans; [ | eassumption ].
  eapply rank_is_linear; eauto using parent_in_D.
Qed.

(* -------------------------------------------------------------------------- *)

(* The index of [x] is defined as the largest [i] such that [i]
   iterations of [A k] take us from [K x] to at most [K (p x)]. *)

Definition i :=
  betaf (fun i => iter i (A k) (K x)) (K (p x)).
  (* If that sounds crazy: it is. *)

(* The following lemmas justify that [i] is well-defined. *)

Lemma i_exists:
  iter 0 (A k) (K x) <= K (p x).
Proof using is_rdsf_F x_non_root.
  clear x_has_nonzero_rank.
  simpl.
  forwards: parent_has_greater_rank; eauto.
  lia.
Qed.

Ltac i th :=
  unfold i; eapply th;
  eauto using iter_i_Akx_tends_to_infinity_along_i, iter_Ak_monotonic_in_i,
    i_exists.

(* [i] is at least 1. *)

Lemma i_ge_1:
  1 <= i.
Proof using is_rdsf_F x_non_root x_has_nonzero_rank.
  (* By definition of [i], we must show that applying [A k] once
     to [K x] takes us below or at [K (p x)]. *)
  i betaf_spec_reciprocal. simpl.
  (* And this is true by definition of [k]. *)
  k betaf_spec_direct. (* wow *)
Qed.

(* [i] is at most [K x]. *)

Lemma i_le_rank:
  i <= K x.
Proof using is_rdsf_F x_non_root x_has_nonzero_rank.
  (* By definition of [i], we must show that applying [1 + K x]
     times the function [A k] to [K x] takes us above [K (p x)]. *)
  i betaf_spec_direct_contrapositive_le.
  (* By definition of [A], the right-hand side of this goal is [A (1 + k) (K x)]. *)
  match goal with |- _ < ?rhs =>
    replace rhs with (A (1 + k) (K x)) by reflexivity
  end.
  (* This goal holds by definition of [k]. *)
  k betaf_spec_reciprocal_contrapositive. (* tchac! *)
Qed.

End NonRoot.

(* -------------------------------------------------------------------------- *)

(* We write [N] for a certain fixed upper bound on the number of vertices.
   This number is part of the definition of the potential function, which
   is why it needs to be fixed up front. The actual number of vertices [n]
   will be allowed to grow as long as it does not exceed [N]. *)

Section N.

Variable N : nat.

(* The potential of a vertex. *)

Definition phi x :=
  If is_root F x \/ K x = 0 then
     alpha N        * K x
  else
    (alpha N - k x) * K x - i x.

(* The total potential. *)

Definition Phi :=
  fold (monoid_make plus 0) phi D.

(* The following lemmas repeat the cases of the definition of [phi]. *)

Lemma phi_case_1a:
  forall x,
  is_root F x ->
  phi x = alpha N * K x.
Proof using.
  clear is_rdsf_F.
  intros. unfold phi. cases_if.
  eauto.
  { false. tauto. }
Qed.

Lemma phi_case_1b:
  forall x,
  K x = 0 ->
  phi x = 0.
Proof using.
  clear is_rdsf_F.
  introv h. unfold phi. cases_if.
  rewrite h. lia.
  { false. tauto. }
Qed.

Lemma phi_case_2:
  forall x,
  ~ is_root F x ->
  0 < K x ->
  phi x = (alpha N - k x) * K x - i x.
Proof using.
  clear is_rdsf_F.
  intros. unfold phi. cases_if.
  { false. branches. tauto. lia. }
  eauto.
Qed.

(* An upper bound on [phi x]. *)

Lemma phi_upper_bound:
  forall x,
  phi x <= alpha N * K x.
Proof using.
  clear is_rdsf_F.
  intros. unfold phi. cases_if.
  eauto.
  lia_rewrite (alpha N - k x <= alpha N).
  lia_rewrite (forall a b, a - b <= a).
  eauto.
Qed.

End N.

End Tarjan.

(* -------------------------------------------------------------------------- *)

(* When [D] is empty, [Phi] is zero. *)

Lemma Phi_empty:
  forall V F K N,
  Phi (\{} : set V) F K N = 0.
Proof using.
  intros. unfold Phi. rewrite fold_empty. reflexivity.
Qed.

(* Extending [D] with a new vertex does not affect [Phi]. This relies on
   our invariant, which guarantees that [K] is zero outside [D]. *)

Lemma Phi_extend:
  forall V D F K N r,
  @is_rdsf V D F K ->
  r \notin D ->
  Phi D F K N = Phi (D \u \{r}) F K N.
Proof using.
  intros.
  unfold Phi.
  rewrite fold_union; eauto with finite typeclass_instances. 2: rew_set in *.
  rewrite fold_single; eauto with typeclass_instances.
  simpl.
  rewrite phi_case_1b by eauto with zero_rank.
  lia.
Qed.

(* -------------------------------------------------------------------------- *)

(* Hints. *)

Hint Resolve k_exists : k.

Hint Resolve i_exists iter_i_Akx_tends_to_infinity_along_i
iter_Ak_monotonic_in_i : i.

Ltac k th :=
  match goal with |- context[k ?F ?K ?x] =>
    eapply th with (f := fun k => A k (K x)); eauto with k monotonic
  end.

Ltac i th :=
  match goal with |- context[i ?F ?K ?x] =>
    eapply th with (f := fun i => iter i (A (k F K x)) (K x)); eauto with i
  end.
