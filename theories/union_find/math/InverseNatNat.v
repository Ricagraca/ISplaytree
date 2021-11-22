(* This module defines two notions of inverse for a function of type
   [nat -> nat] which is monotonic and tends towards infinity. *)

(* We define a lower inverse [betaf] and an upper inverse [alphaf].
   [betaf y] is less than or equal to [alphaf y]. They differ by at
   most one, and they are equal when [y] is in the image of [f]. *)

From TLC Require Import LibTactics LibRelation LibMin.
From iris_time.union_find.math Require Import LibFunOrd LibNatExtra
  Filter FilterTowardsInfinity TLCBuffer.

Section Inverse.

(* -------------------------------------------------------------------------- *)

(* Assumptions. *)

Variable f : nat -> nat.

Variable f_tends_to_infinity:
  limit towards_infinity towards_infinity f.

Variable f_monotonic:
  monotonic le le f.

Variable f_strictly_monotonic:
  monotonic lt lt f.

(* We note that, if [f] is strictly monotonic, then [f] is monotonic.
   So, the two assumptions above might seem redundant. Nevertheless,
   it is useful to state them separately, as some lemmas need only
   the weaker hypothesis [f_monotonic], while some lemmas need the
   stronger hypothesis [f_strictly_monotonic]. *)

(* -------------------------------------------------------------------------- *)

(* Auxiliary lemmas, used in the following. *)

Lemma alphaf_existence:
  forall y,
  exists x, y <= f x.
Proof using f_tends_to_infinity.
  intros.
  generalize (exploit_tends_towards_infinity f_tends_to_infinity y).
  intros [ ? ? ]. eauto.
Qed.

Lemma betaf_bound:
  forall y,
  exists x,
  lower_bound (inverse le) (fun x => f x <= y) x.
Proof using f_tends_to_infinity.
  intros.
  (* Since [f] tends towards infinity, there exists a threshold [x0]
     beyond which this function exceeds [y]. *)
  generalize (exploit_tends_towards_infinity f_tends_to_infinity (y + 1)).
  intros [ x0 hx0 ].
  (* Thus, [f x <= y] implies [x < x0]. *)
  unfold lower_bound, inverse.
  eexists x0.
  intros x ?.
  destruct (Compare_dec.le_gt_dec x x0); [ assumption | ].
  forwards: hx0 x. lia. lia.
Qed.

(* -------------------------------------------------------------------------- *)

(* Because [f] tends towards infinity, for every [y], there exists a least
   [x] such that [f x] is at least [y]. We refer to it as [alphaf y]. *)

Definition alphaf y :=
  MMin (fun x => y <= f x).

(* -------------------------------------------------------------------------- *)

(* By definition, [alphaf y] is the least [x] such that [y <= f x] holds.
   Because [f] is monotonic, this property holds for all [x] above [alphaf y].
   Thus, [y <= f x] is equivalent to [alphaf y <= x]. In that sense, [alphaf]
   is an inverse of [f]. *)

Lemma alphaf_spec_direct:
  forall y x,
  alphaf y <= x ->
  y <= f x.
Proof using f_monotonic f_tends_to_infinity.
  intros.
  transitivity (f (alphaf y)).
  (* The first sub-goal holds by definition of [alphaf]. *)
  mmin_spec (alphaf y).
  eauto using alphaf_existence.
  (* The second sub-goal holds by monotonicity of [f]. *)
  eauto with monotonic.
Qed.

Lemma alphaf_spec_direct_contrapositive:
  forall y x,
  f x < y ->
  x < alphaf y.
Proof using f_tends_to_infinity f_monotonic.
  intros. prove_lt_lt_by_contraposition. eauto using alphaf_spec_direct.
Qed.

Lemma alphaf_spec_reciprocal:
  forall y x,
  y <= f x ->
  alphaf y <= x.
Proof using f_tends_to_infinity.
  intros.
  (* The goal holds by definition of [alphaf]. *)
  mmin_spec (alphaf y).
  eauto using alphaf_existence.
  eapply minimality. assumption.
Qed.

Lemma alphaf_spec_reciprocal_contrapositive:
  forall y x,
  x < alphaf y ->
  f x < y.
Proof using f_tends_to_infinity.
  intros. prove_lt_lt_by_contraposition. eauto using alphaf_spec_reciprocal.
Qed.

Lemma alphaf_spec:
  forall y x,
  (alphaf y <= x <-> y <= f x).
Proof using f_tends_to_infinity f_monotonic.
  split; eauto using alphaf_spec_direct, alphaf_spec_reciprocal.
Qed.

Lemma f_alphaf:
  forall y,
  y <= f (alphaf y).
Proof using f_tends_to_infinity f_monotonic.
  eauto using alphaf_spec_direct.
Qed.

Lemma alphaf_f:
  forall x,
  alphaf (f x) <= x.
    (* If [f] is strictly monotonic, there is equality. See below. *)
Proof using f_tends_to_infinity f_monotonic.
  eauto using alphaf_spec_reciprocal.
Qed.

Lemma alphaf_f_exact:
  forall x,
  alphaf (f x) = x.
Proof using f_tends_to_infinity f_monotonic f_strictly_monotonic.
  intros.
  (* If this equality does not hold, then, by the previous lemma,
     [alphaf (f x)] must be less than [x]. *)
  destruct (Nat.eq_decidable (alphaf (f x)) x); [ assumption | false ].
  assert (h1: alphaf (f x) < x).
    { forwards: alphaf_f x. lia. }
  (* By exploiting the fact that [f] is strictly monotonic and
     the lemma [f_alphaf], we find [f x < f x]. Contradiction. *)
  forwards h2: f_strictly_monotonic h1.
  forwards h3: f_alphaf (f x).
  lia.
Qed.

(* [alphaf] is monotonic. *)

Lemma alphaf_monotonic:
  monotonic le le alphaf.
Proof using f_tends_to_infinity f_monotonic f_strictly_monotonic.
  intros x y ?.
  eapply alphaf_spec_reciprocal.
  rewrite <- f_alphaf.
  assumption.
Qed.

(* -------------------------------------------------------------------------- *)

(* Almost symmetrically, if [f 0 <= y] holds, then there exists a largest [x]
   such that [f x] is bounded by [y]. We refer to it as [betaf y]. Because
   [f] is monotonic, this property holds for all [x] below [betaf y]. Thus,
   [f x <= y] is equivalent to [x <= betaf y]. In that sense, [betaf] is an
   inverse of [f]. *)

Definition betaf y :=
  MMax (fun x => f x <= y).

Lemma betaf_spec_direct:
  forall y x,
  f 0 <= y ->
  x <= betaf y ->
  f x <= y.
Proof using f_tends_to_infinity f_monotonic.
  intros.
  transitivity (f (betaf y)).
  (* The first sub-goal holds by monotonicity of [f]. *)
  eauto with monotonic.
  (* The second sub-goal holds by definition of [betaf]. *)
  mmin_spec (betaf y).
    eauto.
    eauto using betaf_bound.
Qed.

Lemma betaf_spec_direct_contrapositive:
  forall y x,
  f 0 <= y ->
  y < f x ->
  betaf y < x.
Proof using f_tends_to_infinity f_monotonic.
  intros. prove_lt_lt_by_contraposition. eauto using betaf_spec_direct.
Qed.

Lemma betaf_spec_direct_contrapositive_le:
  forall y x,
  f 0 <= y ->
  y < f (1 + x) ->
  betaf y <= x.
Proof using f_tends_to_infinity f_monotonic.
  intros.
  cut (betaf y < 1 + x). lia.
  eauto using betaf_spec_direct_contrapositive.
Qed.

Lemma betaf_spec_reciprocal:
  forall y x,
  f x <= y ->
  x <= betaf y.
Proof using f_tends_to_infinity.
  intros.
  (* The goal holds by definition of [betaf]. *)
  mmin_spec (betaf y).
    eauto. (* [f 0 <= y] not needed, as [f x <= y] implies the desired existence *)
    eauto using betaf_bound.
  eapply minimality. assumption.
Qed.

Lemma betaf_spec_reciprocal_contrapositive:
  forall y x,
  betaf y < x ->
  y < f x.
Proof using f_tends_to_infinity.
  intros. prove_lt_lt_by_contraposition. eauto using betaf_spec_reciprocal.
Qed.

Lemma betaf_spec:
  forall y x,
  f 0 <= y ->
  (x <= betaf y <-> f x <= y).
Proof using f_tends_to_infinity f_monotonic.
  split; eauto using betaf_spec_direct, betaf_spec_reciprocal.
Qed.

Lemma f_betaf:
  forall y,
  f 0 <= y ->
  f (betaf y) <= y.
Proof using f_tends_to_infinity f_monotonic.
  eauto using betaf_spec_direct.
Qed.

Lemma betaf_f:
  forall x,
  x <= betaf (f x).
    (* If [f] is strictly monotonic, there is equality. See below. *)
Proof using f_tends_to_infinity.
  eauto using betaf_spec_reciprocal.
Qed.

Lemma betaf_f_exact:
  forall x,
  x = betaf (f x).
Proof using f_tends_to_infinity f_strictly_monotonic f_monotonic.
  intros.
  (* If this equality does not hold, then, by the previous lemma,
     [x] must be less than [betaf (f x)]. *)
  destruct (Nat.eq_decidable x (betaf (f x))); [ assumption | false ].
  assert (h1: x < betaf (f x)).
    { forwards: betaf_f x. lia. }
  (* By exploiting the fact that [f] is strictly monotonic and
     the lemma [f_betaf], we find [f x < f x]. Contradiction. *)
  forwards h2: f_strictly_monotonic h1.
  forwards h3: f_betaf (f x).
    eauto with monotonic lia.
  lia.
Qed.

(* [betaf] is monotonic. *)

Lemma betaf_monotonic:
  monotonic (fun x y => f 0 <= x <= y) le betaf.
Proof using f_tends_to_infinity f_monotonic.
  intros x y ?.
  eapply betaf_spec_reciprocal.
  rewrite f_betaf by tauto.
  tauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* [alphaf x y] and [betaf x y] are related as follows. *)

(* Because [f] is strictly monotonic, for a fixed [y], there is at most one
   point [x] where [f x = y] holds. This implies that, if [betaf y] is
   defined, then [betaf y] is less than or equal to [alphaf y]. *)

Lemma betaf_le_alphaf:
  forall y,
  f 0 <= y ->
  betaf y <= alphaf y.
Proof using f_tends_to_infinity f_strictly_monotonic f_monotonic.
  intros.
  (* Because [f] is strictly monotonic, it suffices to prove that
     [f (betaf y)] is less than or equal to [f (alphaf y)]. *)
  eapply monotonic_lt_lt_implies_inverse_monotonic_le_le; [ eapply f_strictly_monotonic | ].
  (* The proof is now easy: [y] is between these numbers. *)
  eauto 3 using Nat.le_trans, f_betaf, f_alphaf.
Qed.

(* In the above lemma, if [y] is of the form [f x], then we have equality
   between [betaf y] and [alphaf y], and both are equal to [x]. *)

Lemma betaf_le_alphaf_equality:
  forall y x,
  f x = y ->
  betaf y = alphaf y /\ alphaf y = x.
Proof using f_tends_to_infinity f_strictly_monotonic f_monotonic.
  intros. subst.
  forwards: alphaf_f x.
  forwards: betaf_f x.
  forwards: betaf_le_alphaf (f x).
    { eauto with monotonic lia. }
  split; lia.
Qed.

(* The converse of the above property holds. That is, we have equality
   between [betaf y] and [alphaf y] only if [y] is in the image of [f]. *)

Lemma betaf_le_alphaf_equality_converse:
  forall y x,
  f 0 <= y ->
  betaf y = alphaf y ->
  alphaf y = x ->
  f x = y.
Proof using f_tends_to_infinity f_monotonic.
  introv ? h1 h2.
  forwards h3: f_alphaf y.
  forwards h4: f_betaf y. assumption.
  rewrite h1 in h4. clear h1.
  rewrite h2 in h3, h4. clear h2.
  lia.
Qed.

(* [betaf y] and [alphaf y] differ by at most one. *)

Lemma betaf_alphaf_differ_by_at_most_one:
  forall y,
  alphaf y <= 1 + betaf y.
Proof using f_tends_to_infinity.
  intros.
  (* If the goal does not hold, then there exists [z] which is
     greater than [betaf y] and less than [alphaf y]. *)
  destruct (Compare_dec.le_gt_dec (alphaf y) (1 + betaf y)); [ assumption | false ].
  assert (zz: exists z, betaf y < z < alphaf y).
    { exists (betaf y + 1). lia. }
  destruct zz as [ z [ hz1 hz2 ]].
  (* This [z] has the properties [y < f z] and [f z < y]. Contradiction. *)
  forwards: betaf_spec_reciprocal_contrapositive. eexact hz1.
  forwards: alphaf_spec_reciprocal_contrapositive. eexact hz2.
  lia.
Qed.

(* Because [f] is monotonic, [y < z] implies [betaf y < alphaf z]. *)

Lemma alphaf_lt_betaf:
  forall y z,
  f 0 <= y ->
  y < z ->
  betaf y < alphaf z.
Proof using f_tends_to_infinity f_monotonic.
  intros.
  (* Because [f] is monotonic, it suffices to prove that
     [f (betaf y)] is less than [f (alphaf z)]. *)
  eapply monotonic_le_le_implies_inverse_monotonic_lt_lt.
    eexact f_monotonic.
  (* The proof is now easy: [y < z] are between these numbers. *)
  eauto 4 using Nat.le_lt_trans, Nat.lt_le_trans, f_betaf, f_alphaf.
Qed.

(* [betaf] tends to infinity. *)

Lemma betaf_tends_to_infinity:
  limit towards_infinity towards_infinity betaf.
Proof using f_tends_to_infinity.
  eapply prove_tends_towards_infinity. intro x.
  exists (f x). intros y h.
  eauto using betaf_spec_reciprocal.
Qed.

(* TEMPORARY show that [alphaf] tends to infinity too
   using betaf_le_alphaf
   and a generic proof that if f tends to infinity and f <= g then g tends to infinity *)

End Inverse.

Hint Resolve alphaf_monotonic betaf_monotonic : monotonic typeclass_instances.
