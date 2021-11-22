Set Implicit Arguments.
From TLC Require Import LibTactics LibLogic LibProd LibContainer LibSet
     LibRelation LibPer.
Local Notation path := rtclosure.
From iris_time.union_find.math Require Import TLCBuffer UnionFind01Data.

(* -------------------------------------------------------------------------- *)

Section PathCompression.

(* We now consider what happens when one performs one step of path compression.
   We assume that there is an edge from [x] to [y] and a path from [y] to [z].
   We do not require [z] to be a root, as this is in principle unnecessary. We
   replace the edge of [x] to [y] with an edge from [x] to [z]. *)

Variable V : Type.
Variable F : binary V.
Variable x z : V.

(* Path compression is performed as follows. We first corestrict [F] to [x],
   then take the union with the singleton [per_single x z]. *)

Definition compress : binary V :=
  fun a b => (F a b /\ a <> x) \/ (a = x /\ b = z).

Ltac by_cases_on_compress :=
  unfold compress in *; branches; unpack; subst.

(* We have a new edge from [x] to [z]. *)

Lemma compress_x_z:
  compress x z.
Proof using.
  unfold compress. eauto.
Qed.

(* Every existing edge whose source is not [x] is preserved. *)

Lemma compress_preserves_other_edges:
  forall v w,
  F v w ->
  v <> x ->
  compress v w.
Proof using.
  unfold compress. eauto.
Qed.

Lemma compress_preserves_other_edges_converse:
  forall v w,
  compress v w ->
  v <> x ->
  F v w.
Proof using.
  unfold compress. intros. branches; unpack; subst. eauto. tauto.
Qed.

Lemma compress_preserves_roots_other_than_x:
  forall r,
  r <> x ->
  is_root F r ->
  is_root compress r.
Proof using.
  unfold is_root, not. intros. by_cases_on_compress; eauto.
Qed.

Lemma compress_preserves_roots_converse:
  forall r,
  is_root compress r ->
  is_root F r.
Proof using.
  unfold is_root, compress. intros r hr v ?.
  tests : (r = x); eapply hr; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* The following hypotheses are introduced only now, as they are not needed
   by the above lemmas. *)

Variable y : V.
Hypothesis x_edge_y:  F x y.

(* [is_root] is preserved. *)

Lemma compress_preserves_roots:
  forall r,
  is_root F r ->
  is_root compress r.
Proof using x_edge_y.
  unfold is_root, not. intros. by_cases_on_compress; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* The following hypotheses are introduced only now, as they are not needed
   by the above lemmas. *)

Variable D : set V.
Hypothesis is_dsf_F:  is_dsf D F.
Hypothesis y_path_z:  path F y z.

(* Every path out of [y] is preserved. *)

Lemma compress_preserves_paths_out_of_y:
  forall v w,
  path F v w ->
  path F y v ->
  path compress v w.
Proof using x_edge_y is_dsf_F y_path_z.
  induction 1 using rtclosure_ind_l; [| rename x0 into v, z0 into w ]; intros.
    { eauto with rtclosure. }
    { (* Because there is a path from [y] to [v], [v] cannot be [x],
         as there would otherwise be a cycle. *)
      assert (x <> v).
        { applys* paths_have_distinct_endpoints.
          applys* tclosure_of_rtclosure_r y. }
      (* Thus, we can follow the old edge out of [v]: it is preserved. *)
      eauto using rtclosure_l, rtclosure_r, compress_preserves_other_edges. }
Qed.

(* Every path out of [z] is preserved. *)

Lemma compress_preserves_paths_out_of_z:
  forall v w,
  path F v w ->
  path F z v ->
  path compress v w.
Proof using x_edge_y is_dsf_F y_path_z.
  eauto using compress_preserves_paths_out_of_y, rtclosure_trans_explicit.
Qed.

(* Every path to a root is preserved. *)

Lemma compress_preserves_paths_to_roots:
  forall v r,
  path F v r ->
  is_root F r ->
  path compress v r.
Proof using x_edge_y is_dsf_F y_path_z.
  induction 1 as [| w v r ] using rtclosure_ind_l; intros.
  eauto with rtclosure.
  destruct (classic (x = v)).
    { subst v.
      (* Assume the path begins at [x]. Then, [r] must be the representative
         of [x]. *)
      assert (is_repr F x r).
        { eauto with is_repr. }
      (* Because [x] and [z] are equivalent, [r] is also the representative
         of [z]. *)
      assert (is_repr F z r).
        { eauto with is_repr. }
      (* Hence, there is a path of [z] to [r], and by the previous lemma,
         this path is preserved. Thus, after compression, one can go from
         [x] to [r] by taking the new edge from [x] to [z] and from there
         by following the same path as before. *)
        eapply rtclosure_l.
        eauto using compress_x_z.
        eauto using compress_preserves_paths_out_of_z, is_repr_path with rtclosure. }
    (* If the path does not begin at [x], then its first edge is preserved.
       Just follow it and continue. *)
    { eapply rtclosure_l; eauto using compress_preserves_other_edges. }
Qed.

(* [is_repr] is preserved. *)

Lemma compress_preserves_is_repr_direct:
  forall x r,
  is_repr F x r ->
  is_repr compress x r.
Proof using x_edge_y is_dsf_F y_path_z.
  unfold is_repr. intros. unpack.
  eauto using compress_preserves_paths_to_roots, compress_preserves_roots.
Qed.

Lemma compress_preserves_is_repr_direct':
  forall x r,
  is_root F z ->
  is_repr F x r ->
  is_repr compress x r.
Proof using x_edge_y is_dsf_F y_path_z.
  Hint Unfold is_repr : core.
  intros x' r' Rz [Pr' Rr']. split.
  { induction Pr' as [r'|y' x' z'] using rtclosure_ind_l.
    { now constructor. }
    { tests E: (x' = x).
      { asserts: (y' = y). applys* is_dsf_functional. subst.
        asserts: (z' = z). applys* functional_is_repr y. subst.
        unfold compress. applys* rtclosure_once. }
      { unfold compress. applys* rtclosure_l. } } }
  { applys~ compress_preserves_roots. }
Qed.

(* The structure of a disjoint set forest is preserved. *)

Lemma is_dsf_compress:
  is_dsf D compress.
Proof using x_edge_y is_dsf_F y_path_z.
  splits.
  (* [confined] *)
  { unfold confined. intros. by_cases_on_compress.
      eauto 6 with confined.
      split.
        (* x \in D *) eauto with confined.
        (* z \in D *) eauto with sticky confined. }
  (* [functional] *)
  { unfold functional. intros. repeat by_cases_on_compress;
      try solve [ exploit_functional F; eauto | eauto | false ]. }
  (* [defined]. *)
  { intro v.
    forwards [ r ? ]: is_dsf_defined_is_repr v. eauto.
    eauto using compress_preserves_is_repr_direct. }
Qed.

Hint Resolve is_dsf_compress : functional.

(* [is_repr] is preserved (both ways). *)

Lemma compress_preserves_is_repr:
  is_repr F =
  is_repr compress.
Proof using x_edge_y is_dsf_F y_path_z.
  eapply eq_of_incl_defined_functional.
    unfold rel_incl. eauto using compress_preserves_is_repr_direct.
    eauto using is_dsf_defined_is_repr.
    eauto with functional.
Qed.

(* [is_equiv] is preserved. *)

Lemma compress_preserves_is_equiv:
  is_equiv F =
  is_equiv compress.
Proof using x_edge_y is_dsf_F y_path_z.
  unfold is_equiv. rewrite compress_preserves_is_repr. reflexivity.
Qed.

(* [dsf_per] is preserved. *)

Lemma compress_preserves_dsf_per:
  dsf_per D F =
  dsf_per D compress.
Proof using x_edge_y is_dsf_F y_path_z.
  unfold dsf_per. rewrite compress_preserves_is_equiv. reflexivity.
Qed.

(* The descendants of every root are preserved. *)

Lemma compress_preserves_descendants_of_roots:
  forall r,
  is_root compress r -> (* or: [is_root F r] *)
  descendants compress r = descendants F r.
Proof using x_edge_y is_dsf_F y_path_z.
  intros. eapply set_ext. intros v.
  assert (is_root F r). eauto using compress_preserves_roots_converse.
  repeat rewrite descendant_of_a_root by eauto using compress_preserves_roots.
  rewrite compress_preserves_is_repr.
  tauto.
Qed.

(* No new paths are created. *)

Lemma compress_preserves_paths_converse:
  forall u w,
  path compress u w ->
  path F u w.
Proof using x_edge_y y_path_z. (* note: is_dsf_F not needed *)
  induction 1 as [| v u w ] using rtclosure_ind_l; intros; subst.
  { eauto with rtclosure. }
  { by_cases_on_compress.
    (* Case [u <> x]. This edge cannot be new. *)
    { eauto with rtclosure. }
    (* Case [u = x]. There is a path from [x] to [z] in [F], followed
       with a path from [z] to [w], by the induction hypothesis. *)
    { eauto using rtclosure_trans_explicit with rtclosure. }}
Qed.

(* The ancestors of [y] are not affected. *)

Lemma ancestors_compress:
  ancestors compress y \c ancestors F y.
  (* one could prove an equality, if needed *)
Proof using x_edge_y y_path_z.
  unfold ancestors. intros. eapply incl_prove. intros. rew_set in *.
  eauto using compress_preserves_paths_converse.
Qed.

End PathCompression.

Hint Resolve compress_preserves_roots compress_preserves_roots_converse : is_root.

Ltac by_cases_on_compress :=
  unfold compress in *; branches; unpack; subst.

(* -------------------------------------------------------------------------- *)

(* Two independent steps of path compression commute. *)

Lemma compress_compress:
  forall V F (x1 z1 x2 z2 : V),
  x1 <> x2 ->
  compress (compress F x1 z1) x2 z2 =
  compress (compress F x2 z2) x1 z1.
Proof using.
  intros. unfold compress. extens. intros.
  split; intros; repeat (branches; unpack); subst; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* The following lemmas have weak hypotheses -- they do not rely on the
   hypotheses of the above Section -- and this can be convenient. *)

(* Path compression preserves every path whose origin [y] is not a descendant
   of [x]. *)

Lemma compress_preserves_paths_weak:
  forall V (F : binary V) x y z r,
  path F y r ->
  ~ path F y x ->
  path (compress F x z) y r.
Proof using.
  induction 1 using rtclosure_ind_l; intros.
  { eauto with rtclosure. }
  { eapply rtclosure_l.
      { eauto using compress_preserves_other_edges, not_rtclosure_inv_neq. }
      { eauto with rtclosure. }}
Qed.

(* Path compression preserves the representative of every vertex [y] that is
   not a descendant of [x]. *)

Lemma compress_preserves_is_repr_weak:
  forall V (F : binary V) x y z r,
  is_repr F y r ->
  ~ path F y x ->
  is_repr (compress F x z) y r.
Proof using.
  unfold is_repr. intros. unpack.
  assert (r <> x). { intro. subst. tauto. }
  eauto using compress_preserves_paths_weak, compress_preserves_roots_other_than_x.
Qed.

(* Analogous lemmas, in the reverse direction. *)

Lemma compress_preserves_paths_weak_converse:
  forall V (Fxz : binary V) x y r,
  path Fxz y r ->
  forall F z,
  Fxz = compress F x z ->
  ~ path F y x ->
  path F y r.
Proof using.
  induction 1 using rtclosure_ind_l; intros; subst.
  { eauto with rtclosure. }
  { forwards: compress_preserves_other_edges_converse;
      eauto using not_rtclosure_inv_neq.
    eauto 6 with rtclosure. }
Qed.

Lemma compress_preserves_is_repr_weak_converse:
  forall V (F : binary V) x y z r,
  is_repr (compress F x z) y r ->
  ~ path F y x ->
  is_repr F y r.
Proof using.
  unfold is_repr. intros. unpack.
  eauto using compress_preserves_paths_weak_converse, compress_preserves_roots_converse.
Qed.

(* -------------------------------------------------------------------------- *)

(* If one wishes to reason in terms of the function [R], which maps every
   vertex to its representative, here is how the effect of compression is
   described. *)

(* The agreement between [R] and [is_repr F] is preserved when one applies
   [compress] to [F]. Note that [R] is unchanged, as it should be. *)

Lemma compress_R_compress_agree:
  forall V (D : set V) R F x y z,
  is_dsf D F ->
  fun_in_rel R (is_repr F) ->
  F x y ->
  path F y z ->
  fun_in_rel
    R
    (is_repr (compress F x z)).
Proof using.
  intros. intro w.
  erewrite <- compress_preserves_is_repr by eauto.
  eauto.
Qed.

