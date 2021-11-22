Set Implicit Arguments.
From TLC Require Import LibTactics LibLogic LibProd LibContainer LibSet LibFun
     LibRelation LibPer LibMonoid.
Local Notation path := rtclosure.
From iris_time.union_find.math Require Import LibNatExtra LibIter InverseNatNat
     TLCBuffer
     UnionFind01Data UnionFind04Compress UnionFind11Rank UnionFind21Parent
     UnionFind22ParentEvolution.

(* This file defines the notion of ``pleasantness'' -- the property of having
   a proper non-root ancestor with the same level -- and establishes several
   lemmas which establish an upper bound on the number of unpleasant vertices. *)

(* This reasoning is usually not explicitly carried out on paper, yet it is
   quite lenghty and painful here. *)

(* We parameterize these definitions and lemmas over a predicate [ok] and a
   level function [k], so that they work both for Tarjan's original proof and
   for Alstrup et al.'s proof. *)

(* -------------------------------------------------------------------------- *)

Section Pleasant.

Variable V : Type.

Variable ok : binary V -> (V -> nat) -> V -> Prop.
  (* ok F K x *)

Variable k : (binary V) -> (V -> nat) -> V -> nat.
  (* k F K x *)

(* -------------------------------------------------------------------------- *)

Section FK.

Variable D : set V.
Variable F : binary V.
Variable K : V -> nat.

Hypothesis is_rdsf_F: is_rdsf D F K.
  (* This ensures, in particular, a finite set of ancestors. *)

(* -------------------------------------------------------------------------- *)

(* A non-root vertex [x] is pleasant if it is OK and if it has a proper non-root
   ancestor [y] such that [x] and [y] have the same level, i.e., [k x = k y]. *)

Definition pleasant x :=
  ok F K x /\
  ~ is_root F x /\
  exists y,
  ~ is_root F y /\
  path F (p F x) y /\
  k F K x = k F K y.

Lemma pleasant_non_root:
  forall x,
  pleasant x ->
  ~ is_root F x.
Proof using.
  unfold pleasant. tauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* We define the displeasure of a vertex [x] as the number of unpleasant
   non-root ancestors of [x]. *)

Definition unpleasant_ancestors x :=
  ancestors F x \n \set{ y | ~ pleasant y /\ ~ is_root F y }.

Definition displeasure x :=
  card (unpleasant_ancestors x).

(* -------------------------------------------------------------------------- *)

(* A root has displeasure zero. *)

Lemma displeasure_of_root:
  forall x,
  is_root F x ->
  displeasure x = 0.
Proof using is_rdsf_F.
  intros.
  unfold displeasure, unpleasant_ancestors.
  erewrite ancestors_of_root by eauto with is_dsf.
  rewrite inter_disjoint.
  eapply card_empty.
  set_prove.
Qed.

(* -------------------------------------------------------------------------- *)

(* The following two lemmas relate the displeasure of a non-root vertex [x]
   and the displeasure of its parent [y]. They are an inductive reformulation
   of the definition of [displeasure], in a sense. *)

Lemma displeasure_parent_if_pleasant:
  forall x y,
  F x y ->
  pleasant x ->
  displeasure x = displeasure y.
Proof using is_rdsf_F.
  intros. unfold displeasure, unpleasant_ancestors. f_equal.
  erewrite ancestors_of_parent by eauto with is_dsf.
  eapply inter_union_disjoint_right. set_prove.
Qed.

Lemma displeasure_parent_if_unpleasant:
  forall x y,
  F x y ->
  ~ pleasant x ->
  displeasure x = displeasure y + 1.
Proof using is_rdsf_F.
  intros. unfold displeasure, unpleasant_ancestors.
  erewrite ancestors_of_parent by eauto with is_dsf.
  rewrite <- card_disjoint_union_single with (x := x).
  f_equal.
  eapply inter_union_subset_right.
  { rew_set in *. eauto using a_root_has_no_parent_contrapositive. }
  { eauto 6 with finite is_dsf. }
  { rew_set in *. rew_logic in *. eauto using ancestors_of_parent_disjoint with is_dsf. }
Qed.

(* An upper bound for the above two lemmas. *)

Lemma displeasure_parent:
  forall x y,
  F x y ->
  displeasure x <= displeasure y + 1.
Proof using is_rdsf_F.
  intros.
  tests : (pleasant x).
  { erewrite displeasure_parent_if_pleasant by eauto. lia. }
  { erewrite displeasure_parent_if_unpleasant by eauto. lia. }
Qed.

(* -------------------------------------------------------------------------- *)

Hypothesis ok_hereditary:
  forall x y, ok F K x -> F x y -> ok F K y.

Variable bound : nat.

Hypothesis k_bounded:
  forall x, ok F K x -> ~ is_root F x -> k F K x < bound.

(* -------------------------------------------------------------------------- *)

(* Let us write [levels] for the cardinal of the image under [k] of the set of
   the non-root ancestors of [x]. That is, [levels] is the number of distinct
   levels of the non-root ancestors of [x]. *)

Definition levels x :=
  card (image (k F K) (ancestors F x \n \set{ y | ~ is_root F y })).

(* -------------------------------------------------------------------------- *)

(* If the image of the function [k] is included in the semi-open interval
   [[0, n)], then [levels x] is at most [n]. *)

Lemma bounded_levels:
  forall x,
  ok F K x ->
  levels x <= bound.
Proof using is_rdsf_F ok_hereditary k_bounded.
  intros. unfold levels.
  transitivity (card (interval_as_set 0 bound)).
  { eapply card_le_of_incl; [ eauto using finite_interval_as_set | ].
    unfold image, interval_as_set.
    eapply incl_prove. intros. do 2 (rew_set in *; unpack). subst. split; [ lia | ].
    eapply k_bounded; eauto.
    eapply hereditary_property; eauto.
  }
  { rewrite card_interval_as_set; lia. }
Qed.

(* -------------------------------------------------------------------------- *)

(* The following lemmas relate the levels of a non-root vertex [x] and the
   levels of its parent [y]. *)

Lemma levels_parent_if_pleasant:
  forall x y,
  F x y ->
  levels y <= levels x.
Proof using is_rdsf_F.
  intros. unfold levels.
  eapply card_le_of_incl. { eauto 7 with finite is_dsf. }
  eapply image_covariant.
  eapply inter_covariant.
  eauto using ancestors_of_parent_inclusion with is_dsf.
  reflexivity.
Qed.

Lemma levels_parent_if_unpleasant:
  forall x y,
  F x y ->
  ~ pleasant x ->
  ok F K x ->
  levels y + 1 <= levels x.
  (* one could prove an equality *)
Proof using is_rdsf_F.
  clear ok_hereditary k_bounded.
  intros. unfold levels.
  (* The key remark is that, because [x] is unpleasant, none of its non-root
     ancestors has the same level as [x]. *)
  assert (k F K x \notin image (k F K) (ancestors F y \n \set{ y | ~ is_root F y })).
  { unfold image, ancestors. intro. do 2 (rew_set in *; unpack).
    unfold pleasant in *. rew_logic in *.
    branches.
    { tauto. }
    { eauto using a_root_has_no_parent. }
    { match goal with h: forall x : V, _ |- _ => eapply h end.
      splits; eauto.
      erewrite parent_unique by eauto. assumption. }}
  (* The rest is just administration. *)
  erewrite <- card_disjoint_union_single by eauto 7 with finite is_dsf.
  eapply card_le_of_incl; [ eauto 7 with finite is_dsf | ].
  erewrite ancestors_of_parent with (x := x) by eauto with is_dsf.
  rewrite inter_union_subset_right by (rew_set in *; eauto using a_root_has_no_parent_contrapositive).
  rewrite image_union. rewrite image_singleton.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)

(* By definition of [pleasant], the number of unpleasant non-root ancestors
   of [x] is bounded by [levels x]. *)

Lemma bounded_displeasure_preliminary_1:
  forall x z,
  path F x z ->
  is_root F z ->
  ok F K x ->
  displeasure x <= levels x.
Proof using is_rdsf_F ok_hereditary.
  induction 1 using rtclosure_ind_l; intros.
  (* Base. *)
  { erewrite displeasure_of_root. lia. eauto. }
  (* Step. *)
  { tests : (pleasant x).
    { (* Case: [x] is pleasant. The displeasure of [x] is equal to the
         displeasure of its parent [y]. The set on the right-hand side
         is unchanged because, by definition of [pleasant], [x] admits
         a non-root ancestor with the same level. *)
      assert (hd: displeasure x <= displeasure y).
      { erewrite displeasure_parent_if_pleasant by eauto. eauto. }
      assert (hc: levels y <= levels x).
      { eauto using levels_parent_if_pleasant. }
      rewrite hd. rewrite <- hc. eauto. }
    { (* Case: [x] is unpleasant. The displeasure of [x] is one more
         than the displeasure of its parent [y]. The measure [levels]
         decreases because, by definition of [pleasant], no non-root
         ancestor of [x] has the same level as [x]. *)
      assert (hd: displeasure x <= displeasure y + 1).
      { erewrite displeasure_parent_if_unpleasant by eauto. eauto. }
      assert (hc: levels y + 1 <= levels x).
      { eauto using levels_parent_if_unpleasant. }
      rewrite hd. rewrite <- hc.
      eapply plus_le_plus.
      eauto. }
  }
Qed.

(* -------------------------------------------------------------------------- *)

(* By combining the previous two results, we obtain the following. *)

Lemma bounded_displeasure_preliminary_2:
  forall x,
  ok F K x ->
  displeasure x <= bound.
Proof using is_rdsf_F ok_hereditary k_bounded.
  intros.
  forwards [ z [ ? ? ]]: is_dsf_defined_is_repr x. eauto with is_dsf.
  rewrite bounded_displeasure_preliminary_1 by eauto.
  rewrite bounded_levels by eauto with is_repr.
  eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* As an ad hoc corollary, if every non-root non-OK vertex has an OK parent,
   then we obtain the following bound. This is useful in the special case
   where OK is defined as "non-zero-rank". *)

Lemma bounded_displeasure:
  (forall x y, ~ is_root F x -> ~ ok F K x -> F x y -> ok F K y) ->
  forall x,
  displeasure x <= bound + 1.
Proof using is_rdsf_F ok_hereditary k_bounded.
  intros.
  tests : (ok F K x).
  { rewrite bounded_displeasure_preliminary_2 by eauto. lia. }
  { tests : (is_root F x).
    { erewrite displeasure_of_root by eauto. lia. }
    { unfold is_root in *. rewrite not_forall_not_eq in *. unpack.
      rewrite displeasure_parent by eauto.
      rewrite bounded_displeasure_preliminary_2 by eauto.
      lia. }}
Qed.

End FK.

(* -------------------------------------------------------------------------- *)

(* A step of path compression at [x] does not increase the displeasure of [y],
   the parent of [x]. This sounds obvious, but proving it is pretty dreary.
   This is the object of the following two lemmas. *)

Section Preservation.

Variable D : set V.
Variable F : binary V.
Variable K : V -> nat.

Hypothesis is_rdsf_F: is_rdsf D F K.

Hypothesis compress_preserves_k_above_y:
  forall x y z,
  F x y ->
  path F y z ->
  forall v,
  path F y v ->
  ~ is_root F v ->
  k (compress F x z) K v = k F K v.

Hypothesis compress_preserves_ok_above_y:
  forall x y z,
  F x y ->
  path F y z ->
  forall v,
  path F y v ->
  ~ is_root F v ->
  ok F K v ->
  ok (compress F x z) K v.

Lemma compress_preserves_pleasant_above_y:
  forall x y z,
  F x y ->
  path F y z ->
  forall v,
  path F y v ->
  pleasant F K v ->
  pleasant (compress F x z) K v.
Proof using is_rdsf_F compress_preserves_k_above_y compress_preserves_ok_above_y.
  unfold pleasant. intros. unpack.
  (* Name [av] the ancestor of [v] which has the same level. *)
  match goal with h: path _ _ ?toto |- _ => rename toto into av end.
  assert (x <> v).
  { eapply paths_have_distinct_endpoints; eauto with is_dsf tclosure. }
  assert (path F y (p F v)).
  { eapply rtclosure_trans_explicit; [ eauto | eapply rtclosure_once ].
    eapply parent_spec. eauto. }
  splits; eauto using compress_preserves_roots_converse.
  exists av. splits.
  { eauto using compress_preserves_roots_converse. }
  { eapply compress_preserves_paths_out_of_y; eauto with is_dsf.
    erewrite compress_does_not_change_parent_of_v; eauto.
    erewrite compress_does_not_change_parent_of_v; eauto. }
  { erewrite compress_preserves_k_above_y by eauto.
    erewrite compress_preserves_k_above_y by eauto using rtclosure_trans_explicit.
    assumption. }
Qed.

Lemma compress_preserves_displeasure_of_y:
  forall x y z,
  F x y ->
  path F y z ->
  displeasure (compress F x z) K y <= displeasure F K y.
Proof using is_rdsf_F compress_preserves_k_above_y compress_preserves_ok_above_y.
  unfold displeasure, unpleasant_ancestors. intros.
  eapply card_le_of_incl. eauto 6 with is_dsf finite.
  (* We cannot apply [inter_covariant] and reason separately about each
     side of the intersection, as we need to keep track of the fact that
     we are above [y]. *)
  eapply incl_prove. unfold ancestors. intros. rew_set in *. unpack. splits;
  eauto 6 using compress_preserves_pleasant_above_y,
    compress_preserves_paths_converse, compress_preserves_roots with is_dsf.
Qed.

End Preservation.

End Pleasant.

