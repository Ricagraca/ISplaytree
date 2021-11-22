From TLC Require Import LibTactics.
From iris_time.union_find.math Require Import LibNatExtra LibRewrite.

(* Some lemmas about a potential function of the form [(a - k) * r - i],
   where [k < a] and [0 < r] and [1 <= i <= r]. This function encodes a
   lexicographic ordering on the pair [(k, i)]. When [k] increases, the
   potential function decreases, regardless of [i]. When [k] remains
   constant, the potential function decreases if [i] increases. *)

Lemma lexpo_is_well_defined:
  forall a k r i,
  k < a ->
  i <= r ->
  i <= (a - k) * r.
Proof using.
  intros.
  replace (a - k) with (1 + (a - k - 1)) by lia.
  rewrite Mult.mult_plus_distr_r.
  generalize ((a - k - 1) * r); intro n.
  lia.
Qed.

Lemma lexpo_cannot_increase_if_ak_decreases:
  forall ak ak' r i i',
  i <= r ->
  ak' < ak ->
  ak' * r - i' <= ak * r - i.
Proof using.
  intros.
  assert (h: ak' <= ak - 1). lia.
  rewrite h.
  rewrite Mult.mult_minus_distr_r.
  lia.
Qed.

Lemma lexpo_decreases_if_ak_decreases:
  forall ak ak' r i i',
  i <= r ->
  1 <= i' ->
  0 < ak' ->
  ak' < ak ->
  0 < r ->
  ak' * r - i' < ak * r - i.
Proof using.
  intros.
  (* Use extreme bounds for [i] and [i']. *)
  cut (ak' * r - 1 < ak * r - r). { lia. }
  (* Prove that the left-hand subtraction is well-defined. *)
  assert (0 < ak' * r). { eauto using mult_positive. }
  (* Turn the goal into a large inequality. *)
  cut (ak' * r - 0 <= ak * r - r). { lia. }
  (* Apply the previous lemma. *)
  eauto using lexpo_cannot_increase_if_ak_decreases.
Qed.

Lemma lexpo_cannot_increase:
  forall a k k' r i i',
  i <= r ->
  k <= k' ->
  k' < a ->
  (k = k' -> i <= i') ->
  (a - k) * r - i >= (a - k') * r - i'.
Proof using.
  intros.
  destruct (Nat.eq_decidable k k'); [ subst k' | ].
  (* Case: [k = k']. *)
  { lia. }
  (* Case: [k < k']. *)
  { eauto using lexpo_cannot_increase_if_ak_decreases with lia. }
Qed.

Lemma lexpo_cannot_increase_and_decreases_if:
  forall a k k' r i i',
  i <= r ->
  1 <= i' ->
  i' <= r ->
  k <= k' ->
  k' < a ->
  (k = k' -> i <= i') ->
                          (a - k') * r - i' <= (a - k) * r - i /\
  ( (k < k' \/ i < i') -> (a - k') * r - i' <  (a - k) * r - i ).
Proof using.
  intros.
  destruct (Nat.eq_decidable k k'); [ subst k' | ].
  { (* Case: [k = k']. *)
    split; intros.
    { eapply lexpo_cannot_increase; eauto. }
    { forwards: lexpo_is_well_defined a k r i'; eauto.
      generalize dependent ((a - k) * r); intros n ?.
      (* The upper bound [i' <= n] is useful: since we have [i < i'],
         it gives us [i < n], which is required here. *)
      lia. }
  }
  { (* Case: [k < k']. *)
    split; [ | intros _ ].
    eapply lexpo_cannot_increase; eauto.
    eauto using lexpo_decreases_if_ak_decreases with lia.
  }
Qed.

Lemma prove_lexpo_decreases:
  forall k k' i i',
  k <= k' ->
  (k = k' -> 1 + i <= i') ->
  k < k' \/ i < i'.
Proof.
  intros. lia.
Qed.

(* Now, some seemingly random (in fact very ad hoc) arithmetic lemmas. *)

Lemma random_arithmetic_lemma_00:
  forall a b c d e,
  c <= b ->
  a + b + d <= e + c ->
  a + (b - c + d) <= e.
Proof.
  intros. lia.
Qed.

Lemma random_arithmetic_lemma_01:
  forall ry ary kx ix slack,
  1 <= kx ->
  1 <= ix ->
  kx < ary ->
  ix <= (ary - kx) * ry ->
  ary * (ry + 1 + 1) + ((ary - kx) * ry - ix + 1) <=
  ary * (ry + 1) + ary * (ry + 1) + slack.
Proof.
  introv hkx hix ? ?.
  (* Eliminate the pesky subtraction [ary - kx]. *)
  assert (ary = (ary - kx) + kx). { lia. }
  generalize dependent (ary - kx); intro arykx; intros. subst ary.
  (* Move [ix] to the right-hand side. *)
  eapply random_arithmetic_lemma_00; [ eauto | ].
  (* Use the known bound on [ix]. *)
  rewrite <- hix.
  (* Simplify. *)
  ring_simplify. repeat rewrite <- Mult.mult_assoc.
  generalize dependent (kx * ry); intro krxy.
  (* Conclude. *)
  lia.
Qed.

Lemma random_arithmetic_lemma_02:
  forall ary ry,
  1 <= ary ->
  (ary + 1) * (ry + 1 + 1) + 0 <= ary * (ry + 1) + ary * (ry + 1) + 2.
Proof.
  intros.
  (* Simplify. *)
  ring_simplify. repeat rewrite <- Mult.mult_assoc.
  (* Get rid of the product [ary * ry], while recording that it is at
     least [ry]. *)
  assert (ry <= ary * ry). { eapply mult_magnifies_left. lia. }
  generalize dependent (ary * ry); intros aryry; intros.
  (* Conclude. *)
  lia.
Qed.
