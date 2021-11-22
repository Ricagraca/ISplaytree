Set Implicit Arguments.
From TLC Require Import LibTactics LibLogic LibProd LibContainer LibSet
     LibRelation LibPer.
Local Notation path := rtclosure.
From iris_time.union_find.math Require Import LibNatExtra TLCBuffer
     UnionFind01Data UnionFind02EmptyCreate UnionFind11Rank.

(* -------------------------------------------------------------------------- *)

(* The empty relation, together with the function that assigns rank 0 to every
   vertex, forms a ranked disjoint set forest. *)

Lemma is_rdsf_empty:
  forall V,
  is_rdsf \{} (@empty V) (fun _ => 0).
Proof using.
  intros.
  assert (descendants_empty: forall r, descendants (@empty V) r = \{r}).
    { intros. eapply descendants_outside. eauto using is_dsf_empty. set_prove. }
  splits.
  { eauto using is_dsf_empty. }
  (* Rank increases along edges. *)
  { intros x y. unfold empty. tauto. }
  (* Numerous family. *)
  { repeat intro.
    rewrite descendants_empty.
    rewrite card_single. simpl. lia. }
  (* Finite domain. *)
  { eauto with finite. }
  (* Rank is zero outside of the domain. *)
  { auto. }
Qed.

(* -------------------------------------------------------------------------- *)

(* Creating a new vertex preserves [is_rdsf]. *)

(* We do not need to explicitly extend [K] with a mapping of [x] to [0]
   because we maintain the invariant that [K] is zero outside of [D]. *)

Lemma is_rdsf_create:
  forall V (D : set V) x F K,
  is_rdsf D F K ->
  is_rdsf (D \u \{x}) F K.
Proof using.
  unfold is_rdsf. intros. unpack.
  splits; eauto using is_dsf_create with finite.
  (* Rank is zero outside of the domain. *)
  { intros z ?.
    rew_set in *. rew_logic in *. unpack. eauto. }
Qed.

