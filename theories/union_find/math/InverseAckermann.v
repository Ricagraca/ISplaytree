(* This module defines Tarjan's inverse of Ackermann's function. *)

From TLC Require Import LibTactics LibRelation LibMin.
From iris_time.union_find.math Require Import LibFunOrd LibIter LibNatExtra
     Filter FilterTowardsInfinity Ackermann InverseNatNat.

(* -------------------------------------------------------------------------- *)

(* The function [fun k => A k 1] tends towards infinity. The function [alpha]
   is defined as its upper inverse -- see [InverseNatNat]. *)

Notation alpha :=
  (alphaf (fun k => A k 1)).

(* [alpha] is monotonic. *)

Lemma alpha_monotonic:
  monotonic le le alpha.
Proof using.
  eauto 8 with monotonic typeclass_instances.
Qed.

Hint Resolve alpha_monotonic : monotonic typeclass_instances.

(* -------------------------------------------------------------------------- *)

(* The facts proven about [alphaf] in [InverseNatNat] can be applied to
   [alpha]. The following tactic helps do this; it applies the theorem [th]
   with an appropriate choice of [f], and uses [eauto with monotonic] to prove
   that Ackermann's function is monotonic and tends towards infinity. *)

Ltac alpha th :=
  eapply th with (f := fun k => A k 1);
  eauto with monotonic.

(* Example. *)

Goal
  forall y x,
  alpha y <= x ->
  y <= A x 1.
Proof using.
  intros. alpha alphaf_spec_direct.
Qed.

(* -------------------------------------------------------------------------- *)

(* It takes only [k = 0] to go from [x] to [x + 1]. *)

Lemma beta_x_succ_x:
  forall x,
  x > 0 ->
  betaf (fun k => A k x) (x + 1) = 0.
Proof using.
  intros.
  cut (betaf (fun k => A k x) (x + 1) < 1). { lia. }
  eapply betaf_spec_direct_contrapositive; eauto with monotonic.
    { rewrite Abase_eq. lia. }
    { rewrite A_1_eq. lia. }
Qed.

(* -------------------------------------------------------------------------- *)

(* [alpha] grows very slowly. In particular, of course, it never grows by more
   than one at a time. *)

(* We state this lemma directly in a generalized form that will be useful when
   we later consider the function [alphar] introduced by Alstrup et al. *)

Lemma alpha_grows_one_by_one:
  forall r,
  1 <= r ->
  forall n,
  alphaf (fun k => A k r) (n + 1) <= alphaf (fun k => A k r) n + 1.
Proof.
  intros.
  (* By definition of [alphaf]: *)
  rewrite alphaf_spec by eauto with monotonic.
  (* By definition of [A]: *)
  rewrite (@Nat.add_comm (alphaf (fun k : nat => A k r) n)).
  rewrite Astep_eq. simpl.
  (* Because [r] is at least 1, this iteration is taken at least once.
     Because [A _] is inflationary, we have the following fact. *)
  assert (fact:
    let f := A (alphaf (fun k : nat => A k r) n) in
    f r <= LibIter.iter r f r
  ).
  { simpl.
    eapply iter_at_least_once with (okA := fun _ => True);
    unfold preserves, within; eauto using Nat.le_trans, Ak_inflationary. }
  (* Thus, we simplify: *)
  rewrite <- fact. clear fact.
  (* Furthermore, we have [n <= A (alphaf (fun k : nat => A k r) n) r]. *)
  forwards fact: f_alphaf (fun k => A k r) n; eauto with monotonic.
  (* Thus, we simplify: *)
  rewrite <- fact. clear fact.
  (* Because [n + 1] is [A 0 n], we can transform the goal to: *)
  replace (n + 1) with (A 0 n) by (rewrite Abase_eq; lia).
  (* The goal follows from the fact that [A] is monotonic. *)
  eapply Akx_monotonic_in_k. lia.
  (* Phew! *)
Qed.

Goal
  forall n,
  alpha (n + 1) <= alpha n + 1.
Proof.
  eauto using alpha_grows_one_by_one.
Qed.

(* -------------------------------------------------------------------------- *)

(* As soon as [n] is at least [4], [alpha n] is greater than one. *)

Lemma two_le_alpha:
  forall n,
  4 <= n ->
  2 <= alpha n.
Proof using.
  intros. alpha alphaf_spec_direct_contrapositive.
Qed.

(* -------------------------------------------------------------------------- *)

(* [alpha n] is at most [1 + alpha (log2 n)]. This gives a weak sense of how
   slowly the function [alpha] grows. In fact, the function [log*] would
   satisfy the same property; yet [alpha] grows even more slowly than
   [log*]. *)

(* This property also shows that [alpha n] and [alpha (log2 n)] are
   asymptotically equivalent. This explains why Tarjan and Cormen et al. are
   content with a bound of [alpha n] for the amortized complexity of union and
   find, even though they could easily obtain [alpha (log2 n)]. See Exercise
   21.4-6 in Cormen et al. *)

Lemma alpha_n_O_alpha_log2n:
  forall n,
  16 <= n ->
  alpha n <= 1 + alpha (log2 n).
Proof using.
  intros.
  (* By definition of [alpha n], we have to prove this: *)
  alpha alphaf_spec_reciprocal.
  rewrite Astep_eq. simpl.
  (* Now, the first occurrence of [alpha (log2 n)] in this goal
     is at least [2]. *)
  match goal with |- _ <= A _ ?x =>
    transitivity (A 2 x); [ | eauto using two_le_alpha, prove_le_log2 with monotonic ]
  end.
  (* And, by definition of [alpha], [A (alpha (log2 n)) 1] is at
     least [log2 n]. *)
  transitivity (A 2 (log2 n)); [ | eapply Akx_monotonic_in_x; alpha f_alphaf ].
  (* There remains prove [n <= A 2 (log n)], which intuitively holds because
     [A 2] is an exponential. *)
  eapply A_2_log2_lower_bound.
Qed.
