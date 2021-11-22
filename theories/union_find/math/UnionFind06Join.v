Set Implicit Arguments.
From TLC Require Import LibTactics LibLogic LibProd LibContainer LibSet
     LibRelation LibPer.
Local Notation path := rtclosure.
From iris_time.union_find.math Require Import TLCBuffer UnionFind01Data.

(* The union of two separate disjoint set forests is again a disjoint set forest.
   This is obvious, of course, but takes some work. *)

Section Join.

Variable V : Type.
Variable D1 D2 : set V.
Variable F1 F2 : binary V.

Hypothesis disjointness:
  D1 \# D2.

Hypothesis hdsf1:
  is_dsf D1 F1.

Hypothesis hdsf2:
  is_dsf D2 F2.

(* If [x] is in [D1] and carries an edge in the union of [F1] and [F2], then
   it carries an edge in [F1]. *)

Lemma edge_union_inversion_1:
  forall x,
  x \in D1 ->
  union F1 F2 x = F1 x.
Proof using disjointness hdsf2.
  clear hdsf1.
  intros x D1x. extens; intros y. split.
  { intros Hu. destruct Hu.
    { eauto. }
    { false. rew_set in *. eauto with confined. }
  }
  { left. eauto. }
Qed.

Lemma edge_union_inversion_2:
  forall x,
  x \in D2 ->
  union F1 F2 x = F2 x.
Proof using disjointness hdsf1.
  clear hdsf2.
  intros x D2x. extens; intros y. split.
  { intros Hu. destruct Hu.
    { false. rew_set in *. eauto with confined. }
    { eauto. }
  }
  { right. eauto. }
Qed.

(* The paths in the union of [F1] and [F2] are the union of paths in [F1] and
   the paths in [F2]. *)

Lemma path_union_inversion_left:
  forall x y,
  path (union F1 F2) x y ->
  x \in D1 ->
  path F1 x y.
Proof using disjointness hdsf1 hdsf2.
  induction 1 using rtclosure_ind_l; intros.
  { eauto with rtclosure. }
  { rewrite edge_union_inversion_1 in * by eauto.
    eauto with rtclosure confined. }
Qed.

Lemma path_union_inversion_right:
  forall x y,
  path (union F1 F2) x y ->
  x \in D2 ->
  path F2 x y.
Proof using disjointness hdsf1 hdsf2.
  induction 1 using rtclosure_ind_l; intros.
  { eauto with rtclosure. }
  { rewrite edge_union_inversion_2 in * by eauto.
    eauto with rtclosure confined. }
Qed.

Lemma path_union_inversion:
  forall x y,
  path (union F1 F2) x y ->
  union (path F1) (path F2) x y.
Proof using disjointness hdsf1 hdsf2.
  intros ?? [->| (? & Hu & ?) ]%rtclosure_inv_l.
  { left. eauto with rtclosure. }
  { destruct Hu.
    { forwards: path_union_inversion_left; eauto with confined.
      left. eauto with rtclosure. }
    { forwards: path_union_inversion_right; eauto with confined.
      right. eauto with rtclosure. }
  }
Qed.

Lemma path_join:
  path (union F1 F2) = union (path F1) (path F2).
Proof using disjointness hdsf1 hdsf2.
  extens; intros x y. split.
  { eauto using path_union_inversion. }
  { intros. eapply rel_incl_union_rtclosure. eauto. }
Qed.

(* If [x] is in [D1], then its descendants in the union of [F1] and [F2] are
   its descendants in [F1]. *)

Lemma descendants_join_1:
  forall x,
  x \in D1 ->
  descendants (union F1 F2) x = descendants F1 x.
Proof using disjointness hdsf1 hdsf2.
  unfold descendants. intros x D1x.
  eapply set_ext; intros y. rew_set.
  rewrite path_join.
  split; introv h.
  { destruct h as [ h | h ].
    { eauto. }
    { destruct (rtclosure_inv_l h) as [->|(z&?&?)].
      { eauto with rtclosure. }
      { assert (y \in D2). { eauto with confined. }
        assert (x \in D2). { eauto with sticky. }
        false. rew_set in *. }
    }
  }
  { left. eauto. }
Qed.

Lemma descendants_join_2:
  forall x,
  x \in D2 ->
  descendants (union F1 F2) x = descendants F2 x.
Proof using disjointness hdsf1 hdsf2.
  unfold descendants. intros x D2x.
  eapply set_ext; intros y. rew_set.
  rewrite path_join.
  split; introv h.
  { destruct h as [ h | h ].
    { destruct (rtclosure_inv_l h) as [|(z&?&?)].
      { subst. eauto with rtclosure. }
      { assert (y \in D1). { eauto with confined. }
        assert (x \in D1). { eauto with sticky. }
        false. rew_set in *. }
    }
    { eauto. }
  }
  { right. eauto. }
Qed.

(* To be a root in the union of [F1] and [F2] is to be a root in both [F1] and [F2]. *)

Lemma is_root_join:
  forall x,
  is_root (union F1 F2) x = (is_root F1 x /\ is_root F2 x).
Proof using.
  unfold is_root, union.
  intros. rew_logic. split; intros; unpack.
  { split; intros y; specializes H y; tauto. }
  { intro. unfold not in *. branches; eauto. }
Qed.

(* Unfortunately, it is not the case that [is_repr (union F1 F2)] coincides with
   [union (is_repr F1) (is_repr F2)]. This is because [is_repr] is the identity
   outside the domain. We are able to prove a slightly weaker result. *)

Goal
  forall x y,
  is_repr (union F1 F2) x y ->
  union (is_repr F1) (is_repr F2) x y.
Proof using disjointness hdsf1 hdsf2.
  unfold is_repr. introv [ hpath hroot ].
  rewrite is_root_join in hroot. unpack.
  rewrite path_join in hpath.
  destruct hpath; [ left | right ]; eauto.
Qed.

Lemma is_repr_join_direct_1:
  forall x y,
  is_repr F1 x y ->
  x \in D1 -> (* could be [x \notin D2]; see next lemma *)
  is_repr (union F1 F2) x y.
Proof using disjointness hdsf1 hdsf2.
  unfold is_repr. introv Hu D1x. destruct Hu; unpack;
  rewrite is_root_join; rewrite path_join; splits; eauto.
  { left. eauto. }
  { eapply only_roots_outside_D; eauto.
    assert (y \in D1). { eauto with sticky. }
    rew_set in *. }
Qed.

Lemma is_repr_join_direct_2:
  forall x y,
  is_repr F2 x y ->
  x \notin D1 ->
  is_repr (union F1 F2) x y.
Proof using disjointness hdsf1 hdsf2.
  unfold is_repr. introv Hu D1x. destruct Hu as [ Hp Hr ]; unpack;
  rewrite is_root_join; rewrite path_join; splits; eauto.
  { right. eauto. }
  { eapply only_roots_outside_D; eauto.
    destruct (rtclosure_inv_l Hp) as [|(z&?&?)].
    { subst*. }
    assert (z \in D2). { eauto with confined. }
    assert (y \in D2). { eauto with sticky. }
    rew_set in *. }
Qed.

(* The final result. *)

Lemma is_dsf_join:
  is_dsf (D1 \u D2) (union F1 F2).
Proof using disjointness hdsf1 hdsf2.
  unfold is_dsf in *. intros. splits.
  (* [confined] *)
  { eapply confined_union.
    { eapply confined_contravariant; intuition eauto using incl_union_l, reflexivity. }
    { eapply confined_contravariant; intuition eauto using incl_union_r, reflexivity. }
  }
  (* [functional] *)
  { intuition eauto using functional_union, confined_disjoint_contradiction. }
  (* [defined] *)
  { intros x.
    destruct (classic (x \in D1)).
    (* Case: [x \in D1]. *)
    { destruct hdsf1 as (?&?&h). forwards (y&hy): h x.
      eauto using is_repr_join_direct_1. }
    (* Case: [x \notin D1]. *)
    { destruct hdsf2 as (?&?&h). forwards (y&hy): h x.
      eauto using is_repr_join_direct_2. }
  }
Qed.

End Join.

