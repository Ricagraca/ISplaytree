Set Implicit Arguments.
From TLC Require Import LibTactics LibLogic LibProd LibEpsilon LibContainer
     LibSet LibRelation LibPer LibMonoid.
Local Notation path := rtclosure.
From iris_time.union_find.math Require Import LibNatExtra LibIter LibRewrite
     InverseNatNat Ackermann InverseAckermann MiscArith TLCBuffer
     UnionFind01Data UnionFind11Rank.

(* We now define the parent [p] of a vertex and prove several properties of
   this function. *)

(* -------------------------------------------------------------------------- *)

Section Parent.

(* In the following, we again assume that [F] is a ranked disjoint set forest
   with domain [D] and ranks [K]. *)

Variable V : Type.
Variable D : set V.
Variable F : binary V.
Variable K : V -> nat.
Hypothesis is_rdsf_F:
  is_rdsf D F K.

(* -------------------------------------------------------------------------- *)

(* Remark: in the special case where [R] has type [A->A->Prop],
   one may get away without providing a proof of [Inhab A]. 
  --TEMPORARY from TLC*)

  Definition rel_to_fun' A (R : A -> A -> Prop) (a : A) : A :=
    @rel_to_fun A A (Inhab_of_val a) R a.  


(* For convenience, following Tarjan's notation, let [p x] refer to the parent
   of [x], if it exists. *)

Definition p :=
  rel_to_fun' F.

Section NonRoot.

(* Let [x] be a non-root. *)

Variable x : V.
Hypothesis x_non_root: ~ is_root F x.

(* There is an edge from [x] to its parent. *)

Lemma parent_spec:
  F x (p x).
Proof using x_non_root.
  unfold p, rel_to_fun'. eapply rel_rel_to_fun_of_not_forall. eauto.
Qed.

(* Every edge out of [x] is to its parent. *)

Lemma parent_unique:
  forall y,
  F x y ->
  p x = y.
Proof using is_rdsf_F.
  unfold p, rel_to_fun'. intros. eapply rel_to_fun_eq_of_functional.
  eapply is_rdsf_F. (* miracle! *) assumption.
Qed.

(* The parent of [x] is in [D]. *)

Lemma parent_in_D:
  p x \in D.
Proof using is_rdsf_F x_non_root.
  (* We use the fact that [F] is confined to [D]. *)
  eapply is_rdsf_F. eapply parent_spec.
Qed.

(* The rank of [x] is less than the rank of its parent. *)

Lemma parent_has_greater_rank:
  K x < K (p x).
Proof using is_rdsf_F x_non_root.
  (* Rank increases along edges. *)
  eapply is_rdsf_F. eapply parent_spec.
Qed.

(* There is a path from [x] to its parent. *)

Lemma path_to_parent:
  path F x (p x).
Proof using is_rdsf_F x_non_root.
  eauto using parent_spec with rtclosure.
Qed.

(* [x] is equivalent to its parent. *)

Lemma is_equiv_parent:
  is_equiv F x (p x).
Proof using is_rdsf_F x_non_root.
  eauto using path_is_equiv, path_to_parent with is_dsf.
Qed.

(* If [z] is the representative of [x], then [z] is the
   representative of [x]'s parent, too. *)

Lemma is_repr_parent:
  forall z,
  is_repr F x z ->
  is_repr F (p x) z.
Proof using is_rdsf_F x_non_root.
  eauto 11 using is_equiv_trans, is_equiv_parent, path_is_equiv with is_repr is_dsf.
Qed.

(* Thus, there is path from the parent of [x] to the representative of [x]. *)

Lemma path_from_parent_to_repr:
  forall z,
  is_repr F x z ->
  path F (p x) z.
Proof using is_rdsf_F x_non_root.
  intros. forwards [ ? ? ]: is_repr_parent; eauto.
Qed.

End NonRoot.

End Parent.

(* -------------------------------------------------------------------------- *)

(* [intro_parent F v] introduces a fresh name, say [parent], for the parent
   of [v] in the graph [F]. The assertion [F v parent] is automatically
   introduced as well. *)

Ltac intro_parent F v :=
  (* Prove that there is an edge from [v] to [p F v]. *)
  forwards: parent_spec F v; [
    (* We must prove that [v] has a parent in [F]. *)
    unfold not in *; eauto with is_root
  | (* Now, introduce a fresh name for the parent of [v]. *)
    let parent := fresh "parent" in
    generalize dependent (p F v); intro parent; intros
  ].

