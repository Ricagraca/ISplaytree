Set Implicit Arguments.
From TLC Require Import LibTactics LibLogic LibProd LibContainer LibSet
     LibRelation LibPer.
Local Notation path := rtclosure.
From iris_time.union_find.math Require Import TLCBuffer UnionFind01Data.

(* -------------------------------------------------------------------------- *)

(* In an empty graph, every vertex is its own representative. *)

Lemma is_repr_empty:
  forall V x,
  is_repr (@empty V) x x.
Proof using.
  unfold is_repr, is_root. eauto with rtclosure.
Qed.

(* The empty relation is a disjoint set forest. *)

Lemma is_dsf_empty:
  forall V,
  is_dsf \{} (@empty V).
  (* This would be true of an arbitrary domain [D], but we fix the empty set
     because this is more specific and sufficient for our purposes. *)
Proof using.
  unfold empty.
  repeat split.
    false.
    false.
    eauto using functional_empty.
    intro x. exists x. eapply is_repr_empty.
Qed.

(* -------------------------------------------------------------------------- *)

(* If [F] is a disjoint set forest with respect to some domain [D1], then it
   is also a disjoint set forest with respect to to a larger domain [D2]. In
   other words, introducing new isolated vertices preserves the validity of
   a forest. *)

Lemma is_dsf_covariant_in_D:
  forall V (D1 D2 : set V) F,
  is_dsf D1 F ->
  D1 \c D2 ->
  is_dsf D2 F.
Proof using.
  unfold is_dsf. intros. jauto_set.
    { split; eapply incl_inv; eauto 2 with confined. }
    { eauto. }
    { eauto. }
Qed.

(* -------------------------------------------------------------------------- *)

(* In particular, adding a single isolated vertex is permitted, and the
   effect of this operation on the PER is to add a new equivalence class. *)

Lemma is_dsf_create:
  forall V (D : set V) x F,
  is_dsf D F ->
  is_dsf (D \u \{x}) F.
Proof using.
  intros. eapply is_dsf_covariant_in_D. eauto. eauto using incl_union_l, reflexivity.
Qed.

Lemma dsf_per_create:
  forall V (D : set V) F x,
  is_dsf D F ->
  dsf_per (D \u \{x}) F =
  per_add_node (dsf_per D F) x.
Proof using.
  unfold per_add_node, per_single, union.
  unfold dsf_per, confine.
  intros. extens. intros y z.
  split; intros; unpack.
    { rew_set in *. intuition eauto with sticky. } 
    { branches; unpack; subst; splits; rew_set; (try now apply _); eauto using is_equiv_refl. }
Qed.
