Set Implicit Arguments.
From TLC Require Import LibTactics LibLogic LibProd LibEpsilon LibContainer
     LibSet LibRelation LibPer LibMonoid.
Local Notation path := rtclosure.
From iris_time.union_find.math Require Import LibNatExtra LibIter LibRewrite
     LibFunOrd InverseNatNat Ackermann InverseAckermann MiscArith TLCBuffer
     UnionFind01Data UnionFind11Rank UnionFind21Parent.

(* Following Alstrup et al.'s paper, we now fix a parameter [r] and define
   variants of the level [k], the index [i], and the potential functions [phi]
   and [Phi] that depend on [r]. *)

(* -------------------------------------------------------------------------- *)

Section Alstrup.

(* Fix the parameter [r], and assume [r] is at least 1. *)

Variable r : nat.

Hypothesis r_geq_1:
  1 <= r.

Section Potential.

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

(* Alstrup et al. define the function [alphar] as follows (page 17).
   Note that their definition of [A] is not the same as ours -- they
   index [k] from 1 and up, whereas, following Tarjan, we index [k]
   from 0 and up -- so our definition of [alphar] looks different. *)

Definition defalphar :=
  fun k => A k r.

Definition prealphar n :=
  alphaf defalphar (n + 1).

Definition alphar (n : nat) :=
  prealphar n + 1.

(* [alphar n] is positive. *)

Lemma alphar_positive:
  forall n,
  alphar n > 0.
Proof using.
  clear r_geq_1.
  intros. unfold alphar. lia.
Qed.

(* [alphar] is monotonic. *)

Lemma alphar_monotonic:
  monotonic le le alphar.
Proof using r_geq_1.
  intros m n ?.
  unfold alphar, prealphar, defalphar.
  eapply plus_le_plus.
  eapply alphaf_monotonic; eauto with monotonic.
  eapply plus_le_plus.
  assumption.
Qed.

(* Like [alpha], [alphar] grows at most by one at a time. *)

Lemma alphar_grows_one_by_one:
  forall n,
  alphar (n + 1) <= alphar n + 1.
Proof using r_geq_1.
  intro.
  unfold alphar, prealphar, defalphar.
  eapply plus_le_plus.
  eauto using alpha_grows_one_by_one.
Qed.

(* If [r] is 1, then [alphar n] is as follows. *)

Lemma alphar_one:
  r = 1 ->
  forall n,
  alphar n = alpha (n + 1) + 1.
Proof using.
  intros h n. unfold alphar, prealphar, defalphar. rewrite h. reflexivity.
Qed.

(* [alphar r] is 1. (Exploited on page 18.) *)

Lemma alphar_r:
  alphar r = 1.
Proof using r_geq_1.
  intros. unfold alphar.
  cut (prealphar r <= 0). { lia. }
  unfold prealphar, defalphar.
  eapply alphaf_spec_reciprocal; eauto with monotonic.
  rewrite (@Abase_eq r). lia.
Qed.

(* If [r] is less than [n], then [alphar n] is at least two (page 17). *)

Lemma alphar_geq_two:
  forall n,
  r < n ->
  1 < alphar n.
Proof using r_geq_1.
  intros.
  change 1 with (0 + 1). eapply plus_lt_plus.
  unfold prealphar, defalphar.
  eapply alphaf_spec_direct_contrapositive; eauto with monotonic.
  rewrite Abase_eq. lia.
Qed.

(* [A (prealphar n) r] is greater than [n] (page 17). *)

Lemma A_prealphar_gt:
  forall n,
  n < A (prealphar n) r.
Proof using r_geq_1.
  intros.
  cut (n + 1 <= A (prealphar n) r). { lia. }
  change (A (prealphar n) r) with ((fun k => A k r) (prealphar n)).
  eapply f_alphaf; eauto with monotonic.
Qed.

(* -------------------------------------------------------------------------- *)

(* The function [rankr x] is just the function obtained by adding [r] to the
   rank of each node. *)

Definition rankr x :=
  K x + r.

(* [rankr x] is of course at least [r]. *)

Lemma r_leq_rankr:
  forall x,
  r <= rankr x.
Proof using.
  clear r_geq_1.
  intros. unfold rankr. lia.
Qed.

(* Hence, [rankr x] is positive. *)

Lemma rankr_positive:
  forall x,
  rankr x > 0.
Proof using r_geq_1.
  intros. unfold rankr. lia.
Qed.

Hint Resolve rankr_positive : monotonic.
  (* used in conjunction with Akx_tends_to_infinity_along_k *)

(* [rankr] increases along a path. *)

Lemma rankr_increases_along_a_path:
  forall x y,
  path F x y ->
  rankr x <= rankr y.
Proof using is_rdsf_F.
  intros. unfold rankr. eapply plus_le_plus.
  eauto using rank_increases_along_a_path.
Qed.

(* The function [alphar . rankr] grows along a path. *)

Lemma alphar_rankr_grows_along_a_path:
  forall x y,
  path F x y ->
  alphar (rankr x) <= alphar (rankr y).
Proof using is_rdsf_F r_geq_1.
  eauto using alphar_monotonic, rankr_increases_along_a_path.
Qed.

(* -------------------------------------------------------------------------- *)

Section NonRoot.

(* Let [x] be a non-root. *)

Variable x : V.
Hypothesis x_non_root: ~ is_root F x.

(* The rankr of [x] is less than the rank of its parent. *)

Lemma parent_has_greater_rankr:
  rankr x < rankr (p x).
Proof using is_rdsf_F x_non_root.
  clear r_geq_1.
  unfold rankr.
  forwards: parent_has_greater_rank; eauto.
  lia.
Qed.

(* The function [alphar . rankr] grows along edges. *)

Lemma alphar_rankr_grows_along_edges:
  alphar (rankr x) <= alphar (rankr (p x)).
Proof using is_rdsf_F x_non_root r_geq_1.
  eapply alphar_monotonic.
  forwards: parent_has_greater_rankr.
  lia.
Qed.

Lemma alphar_rankr_grows_along_edges_corollary:
  alphar (rankr x) <> alphar (rankr (p x)) ->
  alphar (rankr x) <  alphar (rankr (p x)).
Proof using is_rdsf_F x_non_root r_geq_1.
  forwards: alphar_rankr_grows_along_edges. lia.
Qed.

(* -------------------------------------------------------------------------- *)

(* The level of [x] is defined as one plus the largest [k] such that
   [A k (rankr x)] is less than or equal to [rankr (p x)]. *)

Definition defk :=
  fun k => A k (rankr x).

Definition prek :=
  betaf defk (rankr (p x)).

Definition k :=
  prek + 1.

(* The following lemma proves that [k] is well-defined. *)

Lemma k_exists:
  A 0 (rankr x) <= rankr (p x).
Proof using is_rdsf_F x_non_root.
  rewrite Abase_eq.
  eapply parent_has_greater_rankr.
Qed.

Ltac k th :=
  eapply th with (f := defk);
  try solve [ unfold defk; eauto using k_exists with monotonic ].

(* The level of [x] seems to be a measure of the distance of the rank
   of [x] and the rank of its parent. In the case where these ranks
   are closest, [rankr (p x)] is [rankr x + 1], so [k] is 1. *)

Lemma k_is_one:
  K (p x) = K x + 1 ->
  k = 1.
Proof using r_geq_1.
  introv h. unfold k, prek.
  assert (f: rankr (p x) = rankr x + 1). { unfold rankr. lia. }
  rewrite f.
  unfold defk.
  rewrite beta_x_succ_x; eauto using rankr_positive.
Qed.

(* In the case where these ranks are furthest away, [rankr x] is [r] and
   [rankr (p x)] is, well, whatever it is. We find that the level [k] is
   less than [alphar (rankr (p x))]. (Page 18.) *)

Lemma k_lt_alphar:
  k < alphar (rankr (p x)).
Proof using is_rdsf_F x_non_root r_geq_1.
  intros.
  (* Eliminate the pesky ... + 1 on either side. *)
  eapply plus_lt_plus.
  (* By definition of [k], it suffices to prove [rankr (p x) < A (prealphar (rankr (p x)) (rankr x)]. *)
  unfold prek.
  k betaf_spec_direct_contrapositive.
  unfold defk.
  (* The lemma [A_prealphar_gt] yields [rankr (p x) < A (prealphar (rankr (p x)))],
     so the goal simplifies as follows. *)
  eapply Nat.lt_le_trans; [ eapply A_prealphar_gt | ].
  (* The result now follows from the fact that [A] is monotonic and [r] is less
     than or equal to [rankr x]. *)
  eapply Akx_monotonic_in_x. eapply r_leq_rankr.
Qed.

(* Another connection between [rankr] at [x] and at [p x]. *)

Lemma rankr_p_x_lt:
  rankr (p x) < A k (rankr x).
Proof using is_rdsf_F x_non_root r_geq_1.
  (* This holds by definition of [k]. *)
  k betaf_spec_reciprocal_contrapositive. (* tchac! *)
  { unfold k, prek. lia. }
Qed.

(* -------------------------------------------------------------------------- *)

(* The index of [x] is defined as the largest [i] such that [i] iterations of
   [A prek] take us from [rankr x] to at most [rankr (p x)]. *)

Definition i :=
  betaf (fun i => iter i (A prek) (rankr x)) (rankr (p x)).
  (* If that sounds crazy: it is. *)

(* The following lemmas justify that [i] is well-defined. *)

Lemma i_exists:
  iter 0 (A prek) (rankr x) <= rankr (p x).
Proof using is_rdsf_F x_non_root.
  clear r_geq_1.
  simpl. generalize parent_has_greater_rankr. lia.
Qed.

Ltac i th :=
  unfold i; eapply th;
  eauto using iter_i_Akx_tends_to_infinity_along_i, iter_Ak_monotonic_in_i,
    i_exists.

(* [i] is at least 1. *)

Lemma i_ge_1:
  1 <= i.
Proof using is_rdsf_F x_non_root r_geq_1.
  (* By definition of [i], we must show that applying [A prek] once
     to [rankr x] takes us below or at [rankr (p x)]. *)
  i betaf_spec_reciprocal. simpl.
  (* And this is true by definition of [k]. *)
  k betaf_spec_direct. (* wow *)
Qed.

(* [i] is at most [rankr x]. *)

Lemma i_le_rank:
  i <= rankr x.
Proof using is_rdsf_F x_non_root r_geq_1.
  (* By definition of [i], we must show that applying [1 + rankr x] times
     the function [A prek] to [rankr x] takes us above [rankr (p x)]. *)
  i betaf_spec_direct_contrapositive_le.
  (* Since [rankr (p x)] is less than [A k (rankr x)], the goal simplifies
     as follows. *)
  eapply Nat.lt_le_trans. eapply rankr_p_x_lt.
  (* Now, by definition of [A], this is in fact an equality. *)
  unfold k. rewrite Nat.add_comm. rewrite Astep_eq. reflexivity.
Qed.

End NonRoot.

(* -------------------------------------------------------------------------- *)

(* The potential of a vertex. *)

Definition phi x :=
  If is_root F x then
     alphar (rankr x) * (rankr x + 1)
  else If alphar (rankr x) = alphar (rankr (p x)) then
    (alphar (rankr x) - k x) * (rankr x) - i x + 1
  else
    0.

(* The total potential. *)

Definition Phi :=
  fold (monoid_make plus 0) phi D.

(* The following lemmas repeat the cases of the definition of [phi]. *)

Lemma phi_case_1:
  forall x,
  is_root F x ->
  phi x = alphar (rankr x) * (rankr x + 1).
Proof using.
  clear r_geq_1 is_rdsf_F.
  intros. unfold phi. cases_if. eauto.
Qed.

Lemma phi_case_2:
  forall x,
  ~ is_root F x ->
  alphar (rankr x) = alphar (rankr (p x)) ->
  phi x = (alphar (rankr x) - k x) * (rankr x) - i x + 1.
Proof using.
  clear r_geq_1 is_rdsf_F.
  intros. unfold phi. repeat cases_if. reflexivity.
Qed.

Lemma phi_case_3:
  forall x,
  ~ is_root F x ->
  alphar (rankr x) <> alphar (rankr (p x)) ->
  phi x = 0.
Proof using.
  clear r_geq_1 is_rdsf_F.
  intros. unfold phi. repeat cases_if. reflexivity.
Qed.

(* This lemma unifies the last two cases above. *)

Lemma phi_case_2_or_3:
  forall x,
  ~ is_root F x ->
  phi x <= (alphar (rankr x) - k x) * (rankr x) - i x + 1.
Proof using.
  clear r_geq_1.
  intros.
  tests : (alphar (rankr x) = alphar (rankr (p x))).
  { rewrite phi_case_2 by assumption. reflexivity. }
  { rewrite phi_case_3 by assumption. lia. }
Qed.

(* In case 2 above, the subtractions are safe: they cannot produce a
   negative number. The first subtraction always produces at least 1,
   while the second subtraction always produces at least 0. *)

Lemma phi_case_2_safe_k:
  forall x,
  ~ is_root F x ->
  alphar (rankr x) = alphar (rankr (p x)) ->
  k x < alphar (rankr x).
Proof using is_rdsf_F r_geq_1.
  introv ? hrank.
  forwards hk: k_lt_alphar; eauto.
  lia.
  (* We note that the equality hypothesis on the ranks is required.
     Indeed, in case 3, we could have [k x = alphar (rankr x)]. *)
Qed.

Lemma phi_case_2_safe_i:
  forall x,
  ~ is_root F x ->
  alphar (rankr x) = alphar (rankr (p x)) ->
  i x <= (alphar (rankr x) - k x) * (rankr x).
Proof using is_rdsf_F r_geq_1.
  introv ? hrank.
  rewrite i_le_rank by eauto.
  eapply mult_magnifies_left.
  forwards: phi_case_2_safe_k; eauto.
  lia.
Qed.

(* In case 1 above, [phi x] is at least 1. (Page 18.) *)

(* This property seems unused, so we do not name it. *)

Goal
  forall x,
  is_root F x ->
  1 <= phi x.
Proof using.
  clear r_geq_1.
  intros. rewrite phi_case_1 by assumption.
  eapply mult_positive.
  (* [alphar] is positive. *)
  { eapply alphar_positive. }
  (* [rankr x + 1] is not zero. *)
  { lia. }
Qed.

(* In case 2 above, [phi x] is at least 1. (Page 18.) *)

Lemma phi_case_2_lower_bound:
  forall x,
  ~ is_root F x ->
  alphar (rankr x) = alphar (rankr (p x)) ->
  1 <= phi x.
Proof using is_rdsf_F r_geq_1.
  introv h1 h2. rewrite phi_case_2 by assumption.
  forwards: phi_case_2_safe_i; eauto.
  lia.
Qed.

(* Alstrup et al. write, on page, 18, "if x is a nonroot leaf, then rankr (x) = r".
   This appears to be false: in the presence of path compression, a nonroot leaf
   can have nonzero rank. (Imagine it used to be a root with nonzero rank and (as
   per the numerous family condition) many descendants; but these descendants were
   removed by path compression.) Thus, I am unable to conclude that phi x = 0.
   This does not seem to be a problem: this remark in not exploited anywhere. *)

(* An upper bound on [phi x]. In any case, [phi x] is at most the formula that
   appears in case 1. *)

Lemma phi_upper_bound:
  forall x,
  phi x <= alphar (rankr x) * (rankr x + 1).
Proof using.
  clear r_geq_1 is_rdsf_F.
  intros. unfold phi. repeat cases_if.
  (* Case 1. *)
  { eauto. }
  (* Case 2. *)
  { lia_rewrite (alphar (rankr x) - k x <= alphar (rankr x)).
    assert (0 < alphar (rankr x)). { eapply alphar_positive. }
    generalize dependent (alphar (rankr x)). intros a ? ?.
    rewrite Nat.mul_add_distr_l.
    generalize (a * rankr x). intro ar.
    lia. }
  (* Case 3. *)
  { assert (forall x, 0 <= x). { intros. lia. }
    eauto. }
Qed.

(* -------------------------------------------------------------------------- *)

(* Check the definitions shown in the paper. *)

Goal
  forall n,
  alphar n = LibMin.mmin le (fun k => A k r >= n + 1) + 1.
Proof.
  reflexivity.
Qed.

Goal
  forall x,
  rankr x = K x + r.
Proof.
  reflexivity.
Qed.

Goal
  forall x,
  k x = mmax le (fun k => rankr (p x) >= A k (rankr x)) + 1.
Proof.
  reflexivity.
Qed.

Goal
  forall x,
  i x = mmax le (fun i => rankr (p x) >= iter i (A (k x - 1)) (rankr x)).
Proof.
  intros.
  replace (k x - 1) with (prek x) by (unfold k; lia).
  reflexivity.
Qed.

Goal
  forall x,
  phi x =
    If is_root F x then
       alphar (rankr x) * (rankr x + 1)
    else If alphar (rankr x) = alphar (rankr (p x)) then
      (alphar (rankr x) - k x) * (rankr x) - i x + 1
    else
      0.
Proof.
  reflexivity.
Qed.

Goal
  Phi = fold (monoid_make plus 0) phi D.
Proof.
  reflexivity.
Qed.

End Potential.

(* -------------------------------------------------------------------------- *)

(* When [D] is empty, [Phi] is zero. *)

Lemma Phi_empty:
  forall V F K,
  Phi (\{} : set V) F K = 0.
Proof using.
  intros. unfold Phi. rewrite fold_empty. reflexivity.
Qed.

(* If [x] is a root and has zero rank, then [phi x] is [r + 1]. *)

Lemma phi_root_zero_rank:
  forall V D F K x,
  @is_rdsf V D F K ->
  is_root F x ->
  K x = 0 ->
  phi F K x = r + 1.
Proof using r_geq_1.
  intros.
  rewrite phi_case_1 by assumption.
  assert (f: rankr K x = r). { unfold rankr. lia. }
  rewrite f.
  rewrite alphar_r by assumption.
  lia.
Qed.

(* Extending [D] with a new vertex augments [Phi] by [r + 1]. This relies on
   our invariant, which guarantees that [K] is zero outside [D]. *)

Lemma Phi_extend:
  forall V D F K x,
  @is_rdsf V D F K ->
  x \notin D ->
  Phi D F K + (r + 1) = Phi (D \u \{x}) F K.
Proof using r_geq_1.
  intros.
  unfold Phi.
  rewrite fold_union; eauto with finite typeclass_instances. 2: rew_set in *.
  rewrite fold_single; eauto with typeclass_instances.
  simpl.
  erewrite phi_root_zero_rank by eauto using only_roots_outside_D with is_dsf zero_rank. (* ha! *)
  reflexivity.
Qed.


End Alstrup.

(* -------------------------------------------------------------------------- *)

(* Hints. *)

Hint Resolve alphar_monotonic : monotonic.

Hint Resolve rankr_positive : monotonic.
  (* used in conjunction with Akx_tends_to_infinity_along_k *)

Hint Resolve k_exists : k.

Hint Resolve i_exists iter_i_Akx_tends_to_infinity_along_i
iter_Ak_monotonic_in_i : i.

Ltac k th :=
  match goal with |- context[prek ?r ?F ?K ?x] =>
    eapply th with (f := defk r K x);
    unfold defk; eauto with k monotonic
  end.

Ltac i th :=
  match goal with |- context[i ?r ?F ?K ?x] =>
    eapply th with (f := fun i =>
      iter i
        (A (prek r F K x))
        (rankr r K x)
    ); eauto with i
  end.
