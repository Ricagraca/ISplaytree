(* This module defines Tarjan's variant of Ackermann's function,
   and establishes some of its properties. *)

From iris_time.union_find.math Require Import LibNatExtra LibFunOrd
  LibIter LibRewrite.

(* -------------------------------------------------------------------------- *)

(* Tarjan's definition, formulated in terms of [iter]. *)

Definition Abase :=
  fun x => 1 + x.

Definition Astep :=
  fun Ak x => iter (1 + x) Ak x.

Definition A k :=
  iter k Astep Abase.

(* -------------------------------------------------------------------------- *)

(* Tarjan's characteristic equations are satisfied. *)

Lemma Abase_eq:
  forall x,
  A 0 x = 1 + x.
Proof using.
  reflexivity.
Qed.

Lemma Astep_eq:
  forall k x,
  A (1 + k) x = iter (1 + x) (A k) x.
Proof using.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)

(* Closed forms for [A 1] and [A 2], from Cormen et al. *)

Lemma A_1_eq:
  forall x,
  A 1 x = 2 * x + 1.
Proof using.
  assert (fact: forall x y, iter x (A 0) y = x + y).
    induction x; intros; simpl.
    auto.
    rewrite IHx. auto.
  intro x.
  rewrite Astep_eq.
  rewrite fact.
  lia.
Qed.

Lemma iter_A_1_eq:
  forall i x,
  iter i (A 1) x =
  2^i * (1 + x) - 1.
Proof using.
  Opaque plus. (* TEMPORARY ugly *)
  induction i; simpl; intros.
  lia.
  rewrite A_1_eq. rewrite IHi.
  (* Now for some pain... *)
  assert (0 < 2^i). { eauto using power_positive. }
  assert (0 < 1+x). { lia. }
  generalize dependent (2^i); intro n; intros.
  generalize dependent (1+x); intro y; intros.
  assert (0 < n * y). { eauto using mult_positive. }
  rewrite <- Mult.mult_assoc.
  generalize dependent (n * y); intros ny; intros.
  lia. (* phew! *)
  Transparent plus.
Qed.

Lemma A_2_eq:
  forall x,
  A 2 x = 2^(1 + x) * (1 + x) - 1.
Proof using.
  intros. rewrite Astep_eq. eapply iter_A_1_eq.
Qed.

(* -------------------------------------------------------------------------- *)

(* Every [A k] is inflationary. That is, [x <= A k x] holds. *)

Local Notation everywhere :=
  (fun _ => True).

Local Notation inflationary_ :=
  (inflationary everywhere le).

Lemma inflationary_Abase:
  inflationary_ Abase.
Proof using.
  unfold inflationary, Abase. intros. lia.
Qed.

Lemma preserves_inflationary_Astep:
  preserves inflationary_ Astep.
Proof using.
  unfold preserves, within, inflationary, Astep. intros.
  eapply iter_inflationary with (okA := everywhere);
    unfold preserves, within;
    eauto using Nat.le_trans.
Qed.

Lemma Ak_inflationary:
  forall k,
  inflationary_ (A k).
Proof using.
  intro. unfold A.
  eapply iter_invariant.
    eapply inflationary_Abase.
    eapply preserves_inflationary_Astep.
Qed.

Lemma iter_Ak_inflationary:
  forall n k x,
  x <= iter n (A k) x.
Proof using.
  intros.
  (* Kind of reproving the same thing again... *)
  eapply iter_inflationary with (okA := everywhere);
    unfold preserves, within;
    eauto using Nat.le_trans, Ak_inflationary.
Qed.

(* -------------------------------------------------------------------------- *)

(* [Astep] is inflationary. That is, for every inflationary function [Ak],
   [Ak <= Astep Ak] holds -- this is a pointwise inequality. *)

Lemma inflationary_Astep:
  inflationary inflationary_ (pointwise everywhere le) Astep.
Proof using.
  unfold inflationary, pointwise, Astep. intros.
  simpl. rewrite iter_iter_1.
  eapply iter_inflationary with (okA := everywhere);
    unfold preserves, within; eauto using Nat.le_trans.
Qed.

(* -------------------------------------------------------------------------- *)

(* The function [A] is monotonic. (That is, it is monotonic in its first
   argument [k], and the results, which are functions, are compared using
   pointwise inequality.) *)

Lemma A_monotonic:
  monotonic le (pointwise everywhere le) A.
Proof using.
  unfold A.
  (* We must prove that [iter k Astep Abase] is monotonic with respect to [k].
     Because the lemma [inflationary_Astep] has an inflation hypothesis, we
     must carry the information that [A k] is inflationary. This is done by
    picking an appropriate [okA]. *)
  eapply iter_monotonic_in_n_specialized with (okA := inflationary_);
    unfold pointwise; eauto using Nat.le_trans, inflationary_Abase,
    preserves_inflationary_Astep, inflationary_Astep.
Qed.

(* As a corollary, the function [fun k => A k x] is monotonic. In other
   words, Ackermann's function is monotonic in its first argument. *)

Lemma Akx_monotonic_in_k:
  forall x,
  monotonic le le (fun k => A k x).
Proof using.
  (* Forgetting [x], it suffices to argue that [A] is monotonic. *)
  intro.
  eapply monotonic_pointwise_specialize with (okB := everywhere);
    eauto using A_monotonic.
Qed.

Hint Resolve Akx_monotonic_in_k : monotonic typeclass_instances.

(* Example. *)

Goal
  forall k1 k2 x, k1 <= k2 -> A k1 x <= A k2 x.
Proof using.
  eauto with monotonic. (* cool *)
Qed.

(* -------------------------------------------------------------------------- *)

(* The function [fun x => A k x] is monotonic. In other words, Ackermann's
   function is monotonic in its second argument. *)

Lemma monotonic_Abase:
  monotonic le le Abase.
Proof using.
  unfold monotonic, Abase. intros. lia.
Qed.

Lemma preserves_monotonic_Astep:
  forall f,
  inflationary_ f ->
  monotonic le le f ->
  monotonic le le (Astep f).
Proof using.
  intros. intros x1 x2 ?. unfold Astep.
  eapply Nat.le_trans; [ | eapply iter_monotonic_in_x; eauto ].
  eapply iter_monotonic_in_n with (okA := everywhere);
    unfold preserves, within; eauto using Nat.le_trans.
  lia.
Qed.

Lemma Akx_monotonic_in_x:
  forall k,
  monotonic le le (A k).
Proof using.
  (* Because the lemma [preserves_monotonic_Astep] has an inflation
     hypothesis, we argue simultaneously that [A k] is inflationary
     and monotonic. This is a little redundant, but seems acceptable. *)
  cut (forall k, inflationary_ (A k) /\ monotonic le le (A k)).
    { intro h. eapply h. }
  intro. unfold A.
  eapply iter_invariant; split; simpl in *;
  intuition eauto using inflationary_Abase, monotonic_Abase,
    preserves_inflationary_Astep, preserves_monotonic_Astep.
Qed.

Hint Resolve Akx_monotonic_in_x Akx_monotonic_in_k : monotonic typeclass_instances.

(* Example. *)

Goal
  forall k x1 x2, x1 <= x2 -> A k x1 <= A k x2.
Proof using.
  eauto with monotonic. (* cool *)
Qed.

(* -------------------------------------------------------------------------- *)

(* The power function [pow] can be defined in terms of [iter]. *)

Lemma pow_iter:
  forall x y,
  x ^ y = iter y (fun a => x * a) 1.
Proof using.
  induction y; simpl; eauto.
Qed.

(* [2 ^ x <= A 2 x]. *)

Lemma A_2_lower_bound:
  forall x,
  2 ^ x <= A 2 x.
Proof using.
  (* Tarjan's course notes claim a strict inequality, but in fact there
     is equality when [x] is zero. *)
  intro.
  rewrite pow_iter.
  rewrite Astep_eq.
  rewrite iter_iter_1p.
  rewrite A_1_eq.
  (* We are now comparing two applications of [iter]. It suffices to
     exploit the fact that [iter n f x] is monotonic in [f] and [x]. *)
  eapply Nat.le_trans; [ eapply iter_monotonic_in_f | eapply iter_monotonic_in_x ].
    (* from [iter_monotonic_in_f] *)
    eauto.
    eauto using Nat.le_trans.
    split.
      eauto with monotonic.
      unfold pointwise. intros. rewrite A_1_eq. lia.
    (* from [iter_monotonic_in_x] *)
    eauto with monotonic.
    lia.
Qed.

(* A slightly more powerful version of the previous lemma. It is not a
   direct consequence of the previous lemma, because [2 ^ (log2 n)] is
   in general less than or equal to [n]. *)

Lemma A_2_log2_lower_bound:
  forall n,
  n <= A 2 (log2 n).
Proof using.
  (* It is somewhat miraculous that this auxiliary assertion holds. *)
  assert (forall b n, n <= 2 * iter (log2 n) (A 1) b + 1).
  { intros. eapply (log2_induction (fun k n => n <= 2 * iter k (A 1) b + 1)). lia. lia.
    intros. simpl. rewrite A_1_eq. eauto with div2. }
  intros. rewrite Astep_eq. simpl. rewrite A_1_eq. eauto.
  (* An alternative proof would consist in using [A_2_eq] together
     with the fact that [2^(1 + log2 n)] is at least [n + 1]. *)
Qed.

(* [2 ^ (2 ^ ( ... 2)) { x + 1 times } <= A 3 x]. *)

Lemma A_3_lower_bound:
  forall x,
  iter (1 + x) (fun a => 2 ^ a) 0 <= A 3 x.
Proof using.
  intro.
  rewrite Astep_eq.
  (* We are now comparing two applications of [iter]. It suffices to
     exploit the fact that [iter n f x] is monotonic in [f] and [x]. *)
  eapply Nat.le_trans; [ eapply iter_monotonic_in_f | eapply iter_monotonic_in_x ].
    (* from [iter_monotonic_in_f] *)
    eauto.
    eauto using Nat.le_trans.
    split.
      eauto with monotonic.
      unfold pointwise. eauto using A_2_lower_bound.
    (* from [iter_monotonic_in_x] *)
    eauto with monotonic.
    lia.
Qed.

(* -------------------------------------------------------------------------- *)

From iris_time.union_find.math Require Import Filter.
From iris_time.union_find.math Require Import FilterTowardsInfinity.

(* For every [k], the function [fun x => A k x] tends towards infinity. *)

Lemma Akx_tends_to_infinity_along_x:
  forall k,
  limit towards_infinity towards_infinity (fun x => A k x).
Proof using.
  intro.
  eapply prove_tends_towards_infinity.
  (* It suffices to exploit the fact that [A k] is inflationary,
     i.e. [x <= A k x] holds. *)
  intros. exists y. intros ? h.
  rewrite h. eapply Ak_inflationary; eauto.
Qed.

(* For every [x] greater than zero, the function [fun k => A k x] tends
   towards infinity. We prove this via a very weak lower bound, namely
   [k <= A k x]. *)

Lemma Ax_inflationary:
  forall x,
  x > 0 ->
  inflationary_ (fun k => A k x).
Proof using.
  unfold inflationary.
  intros x ? k _.
  induction k; intros; simpl.
  (* Base. *)
  lia.
  (* Step. *)
  rewrite Astep_eq.
  (* [1 + x] is at least 2, and [iter] is monotonic in [n]. *)
  transitivity (iter 2 (A k) x).
    2: eapply iter_monotonic_in_n_specialized with (okA := everywhere);
         unfold preserves, within;
         eauto using Nat.le_trans, Ak_inflationary
                with lia.
  (* Unfold [iter], and exploit the induction hypothesis (which is
     possible because [A k] is monotonic). *)
  simpl.
  transitivity (A k k).
    2: eauto with monotonic.
  (* Now, [A k k] is at least [A 0 k]. *)
  transitivity (A 0 k).
    2: eauto with monotonic lia.
  (* And [A 0 k] is precisely [1 + k]. *)
  rewrite Abase_eq at 1.
  lia.
Qed.

Lemma Akx_tends_to_infinity_along_k:
  forall x,
  x > 0 ->
  limit towards_infinity towards_infinity (fun k => A k x).
Proof using.
  intros.
  eapply prove_tends_towards_infinity.
  intros. exists y. intros.
  rewrite Ax_inflationary by eauto.
  eauto with monotonic.
Qed.

Hint Resolve Akx_tends_to_infinity_along_k : monotonic typeclass_instances.
  (* exploited in [InverseAckermann.v] *)

(* -------------------------------------------------------------------------- *)

(* Every [A k] is strictly inflationary. That is, [x < A k x] holds. *)

Lemma Ak_strictly_inflationary:
  forall k x,
  x < A k x.
Proof using.
  (* [A 0] is strictly inflationary already, and [A k] is no less than
     [A 0]. The result follows by transitivity. *)
  intros.
  assert (x < A 0 x).
    { rewrite Abase_eq. lia. }
  assert (A 0 x <= A k x).
    { eauto with monotonic lia. }
  lia.
Qed.

(* For every [n] other than zero, [iter n (A k)] is strictly inflationary. *)

Lemma iter_Ak_strictly_inflationary:
  forall n k x,
  n > 0 ->
  x < iter n (A k) x.
Proof using.
  intros. destruct n; [ lia | ]. simpl.
  assert (x < A k x).
    { eapply Ak_strictly_inflationary. }
  assert (A k x <= A k (iter n (A k) x)).
    { eauto using iter_Ak_inflationary with monotonic. }
  lia.
Qed.

(* -------------------------------------------------------------------------- *)

(* The function [fun k => A k x] is strictly monotonic in [k]. *)

Lemma Akx_strictly_monotonic_in_k_step:
  forall k x,
  x > 0 ->
  A k x < A (1 + k) x.
Proof using.
  intros. rewrite Astep_eq. simpl. rewrite iter_iter_1.
  eauto using iter_Ak_strictly_inflationary.
Qed.

Lemma Akx_strictly_monotonic_in_k:
  forall x,
  x > 0 ->
  monotonic lt lt (fun k => A k x).
Proof using.
  intros. intros k1 k2 ?.
  assert (A k1 x < A (1 + k1) x).
    { eauto using Akx_strictly_monotonic_in_k_step. }
  assert (A (1 + k1) x <= A k2 x).
    { eauto with monotonic lia. }
  lia.
Qed.

Hint Resolve Akx_strictly_monotonic_in_k : monotonic typeclass_instances.

(* -------------------------------------------------------------------------- *)

(* The orbit of a strictly inflationary function goes to infinity. *)

Lemma iter_strictly_inflationary_tends_to_infinity:
  forall f x,
  (forall x, x < f x) ->
  limit towards_infinity towards_infinity (fun i => iter i f x).
Proof using.
  (* This lemma has nothing to do with Ackermann's function and could
     be placed in a separate file. *)
  (* A strictly inflationary function grows by at least one at each
     iteration, so we can give a linear lower bound for it. This
     implies that iterating over and over takes us to infinity. *)
  intros f x hinfl.
  assert (bound: forall i, x + i <= iter i f x).
  { intro. eapply iter_indexed_invariant; [ | lia ]. intros j y ?.
    generalize (hinfl y). lia. }
  (* Manual proof. *)
  eapply prove_tends_towards_infinity.
  intro y. exists y. intros z ?.
  generalize (bound z). lia.
Qed.

(* The orbit of [A k] out of [x] goes to infinity. *)

Lemma iter_i_Akx_tends_to_infinity_along_i:
  forall k x,
  limit towards_infinity towards_infinity (fun i => iter i (A k) x).
Proof using.
  eauto using iter_strictly_inflationary_tends_to_infinity, Ak_strictly_inflationary.
Qed.

(* Iterating [i] times an inflationary function [f] yields a monotonic function
   of [i]. *)

Lemma iter_inflationary_monotonic:
  forall f x,
  (forall x, x <= f x) ->
  monotonic le le (fun i => iter i f x).
Proof using.
  intros f x hinfl i j ?.
  replace j with ((j - i) + i) by lia.
  rewrite iter_iter.
  generalize (iter i f x). intro y.
  eapply iter_inflationary with (okA := everywhere);
    unfold preserves, within, inflationary; eauto using Nat.le_trans.
Qed.

(* [fun i => iter i (A k) x] is monotonic. *)

Lemma iter_Ak_monotonic_in_i:
  forall k x,
  monotonic le le (fun i => iter i (A k) x).
Proof using.
  intros.
  eapply iter_inflationary_monotonic.
  intro. eapply Ak_inflationary. tauto.
Qed.
