Set Implicit Arguments.
Generalizable All Variables.
From TLC Require Import LibTactics.
From iris_time.union_find.math Require Import LibNatExtra Filter.

(* [le m] can be understood as the semi-open interval of the natural numbers
   that are greater than or equal to [m]. The subsets [le m] form a filter
   base; that is, if we close them under inclusion, then we obtain a filter,
   which intuitively represents going to infinity. We call this modality
   [towards_infinity]. *)

Definition towards_infinity (F : nat -> Prop) :=
  exists m, forall n, m <= n -> F n.

Instance filter_towards_infinity : Filter towards_infinity.
Proof.
  unfold towards_infinity. econstructor.
  (* There exists an element in this filter, namely the universe, [le 0]. *)
  exists (fun n => 0 <= n). eauto.
  (* Every set of the form [le m] is nonempty. *)
  introv [ m ? ]. exists m. eauto.
  (* Closure by intersection and subset. *)
  introv [ m1 ? ] [ m2 ? ] ?. exists (max m1 m2). intros.
  max_case; eauto with lia.
Qed.

(* Every subset of the form [le m] is a member of this filter. *)

Lemma towards_infinity_le:
  forall m,
  towards_infinity (le m).
Proof.
  unfold towards_infinity. eauto.
Qed.

Hint Resolve towards_infinity_le : filter.

(* The statement that [f x] tends towards infinity as [x] tends
   towards infinity can be stated in its usual concrete form or
   more abstractly using filters. *)

Lemma prove_tends_towards_infinity:
  forall f : nat -> nat,
  (forall y, exists x0, forall x, x0 <= x -> y <= f x) ->
  limit towards_infinity towards_infinity f.
Proof.
  introv h. intros F [ m ? ].
  generalize (h m); intros [ x0 ? ].
  exists x0. eauto.
Qed.

Lemma exploit_tends_towards_infinity:
  forall f : nat -> nat,
  limit towards_infinity towards_infinity f ->
  (forall y, exists x0, forall x, x0 <= x -> y <= f x).
Proof.
  intros ? hlimit y.
  forwards [ x0 ? ]: hlimit (le y).
    eapply towards_infinity_le.
  eauto.
Qed.

