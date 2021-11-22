Set Implicit Arguments.
From TLC Require Import LibTactics LibLogic LibFun LibProd LibContainer
     LibSet LibRelation LibPer.
Local Notation path := rtclosure.
From iris_time.union_find.math Require Import TLCBuffer UnionFind01Data.

(* -------------------------------------------------------------------------- *)

Section Link.

(* We now consider what happens when one installs a new link from [x] to [y],
   where [x] and [y] are distinct roots and are in the domain D. *)

Variable V : Type.
Variable D : set V.
Variable F : binary V.
Variable x y : V.

Hypothesis is_dsf_F:  is_dsf D F.
Hypothesis x_in_D:    x \in D.
Hypothesis y_in_D:    y \in D.
Hypothesis is_root_x: is_root F x.
Hypothesis is_root_y: is_root F y.
Hypothesis distinct:  x <> y.

(* The link is installed as follows. *)

Definition link :=
  union F (per_single x y).

(* This does install an edge from [x] to [y]. *)

Lemma link_appears:
  link x y.
Proof using.
  unfold link, union, per_single. eauto.
Qed.

(* This preserves every pre-existing edge. *)

Lemma link_previous:
  forall w z,
  F w z ->
  link w z.
Proof using.
  unfold link, union, per_single. eauto.
Qed.

(* Installing the new link preserves [functional]. *)

Lemma functional_link:
  functional link.
Proof.
  unfold link, union, per_single. intros.
  intros x' y' z' ? ?. repeat branches; unpack; subst;
    try solve [ false; eauto using a_root_has_no_parent ].
    { exploit_functional F. eauto. }
    { eauto. }
Qed.

(* Every vertex that could reach [x] can now reach [y]. *)

Lemma path_link_1:
  forall w,
  path F w x ->
  path link w y.
Proof.
  unfold link, union, per_single.
  induction 1 using rtclosure_ind_l; eauto with rtclosure.
Qed.

(* Every pre-existing path is preserved. *)

Lemma path_link_2:
  forall w z,
  path F w z ->
  path link w z.
Proof.
  unfold link, union, per_single.
  induction 1 using rtclosure_ind_l; eauto with rtclosure.
Qed.

(* Every root other than [x] remains a root. *)

Lemma is_root_link:
  forall z,
  is_root F z ->
  x <> z ->
  is_root link z.
Proof.
  unfold is_root, link, union, per_single, not.
  intuition eauto.
Qed.

(* Every vertex whose representative was [x] now has representative [y]. *)

Lemma is_repr_link_1:
  forall w,
  is_repr F w x ->
  is_repr link w y.
Proof.
  unfold is_repr. intuition eauto using path_link_1, is_root_link.
Qed.

(* Every vertex whose representative was some vertex [r] other than [x] still
   has representative [r]. *)

Lemma is_repr_link_2:
  forall w r,
  is_repr F w r ->
  r <> x ->
  is_repr link w r.
Proof.
  unfold is_repr. intuition eauto using path_link_2, is_root_link.
Qed.

(* Installing the new link preserves [defined]. *)

Lemma defined_link:
  defined (is_repr link).
Proof.
  (* Let [w] be an arbitrary vertex. Let [r] be its representative. *)
  intros w. forwards [ r ? ]: is_dsf_defined_is_repr w. eauto.
  destruct (classic (r = x)).
    (* If [r] is [x], then, after linking, [w] has representative [y]. *)
    { exists y. subst r. eauto using is_repr_link_1. }
    (* If [r] is not [x], then, after linking, [x'] still has representative [r]. *)
    { exists r. eauto using is_repr_link_2. }
Qed.

(* Installing the new link preserves [is_dsf]. *)

Lemma is_dsf_link:
  is_dsf D link.
Proof.
  unfold is_dsf, link. eauto 6 using functional_link, defined_link with confined.
Qed.

(* The effect of the new link on [is_equiv] is to fuse the equivalence classes
   of [x] and [y]. *)

Lemma is_equiv_per_add_edge:
  is_equiv link =
  per_add_edge (is_equiv F) x y.
Proof.
  (* This short, algebraic proof relies on the fact that we already have a
     characterization of [is_equiv F] -- it is the reflexive, symmetric,
     transitive closure of [F] -- and a similar characterization of [is_equiv
     link]. *)
  erewrite is_equiv_rstclosure by eapply is_dsf_link.
  erewrite is_equiv_rstclosure by eauto.
  unfold per_add_edge, link.
  (* There remains to prove a basic fact about unions and closures, which
     is relatively easy to establish. *)
  rewrite stclosure_eq_rstclosure_of_refl by eauto using refl_union_l, refl_rstclosure.
  eapply antisym_rel_incl.
  { eauto using covariant_rstclosure, covariant_union, rel_incl_rstclosure, refl_rel_incl. }
  { eapply rel_incl_rstclosure_rstclosure.
    eapply trans_rel_incl; [ | eapply rel_incl_union_rstclosure ].
    eauto using covariant_union, rel_incl_rstclosure, incl_refl. }
  (* This proof replaces an earlier proof which was much longer and required
     no less than 8 auxiliary lemmas relating the post-state and the pre-state
     (drawing conclusions about the past from hypotheses about the future).
     See attic/UnionFindMath.v. *)
Qed.

(* Confinement within [D] commutes with the addition of this edge. *)

Lemma per_add_edge_confine:
  per_add_edge (confine D (is_equiv F)) x y =
  confine D (per_add_edge (is_equiv F) x y).
Proof.
  unfold per_add_edge.
  assert (x \in D <-> y \in D). { tauto. }
  rewrite confine_stclosure by eauto with sticky.
  f_equal.
  eauto using confine_union_left, confined_per_single.
Qed.

(* The effect of the new link on [dsf_per] is to fuse the equivalence classes
   of [x] and [y]. *)

Lemma dsf_per_add_edge:
  dsf_per D link =
  per_add_edge (dsf_per D F) x y.
Proof.
  unfold dsf_per.
  rewrite per_add_edge_confine.
  rewrite is_equiv_per_add_edge.
  reflexivity.
Qed.

(* Every vertex [r] that is a root after the link was already a root before
   the link, and is not [x]. *)

Lemma is_root_link_converse:
  forall z,
  is_root link z ->
  is_root F z.
Proof.
  unfold is_root, link, union, per_single, not. intuition eauto.
Qed.

Lemma is_root_link_not_x:
  forall z,
  is_root link z ->
  z <> x.
Proof.
  unfold is_root, link, union, per_single, not. eauto.
Qed.

Lemma x_no_longer_a_root:
  ~ is_root link x.
Proof.
  intro.
  forwards: is_root_link_not_x x. assumption.
  tauto.
Qed.

(* If a path from [w] to [y] exists after the link, then before the link there
   was a path from [w] to either [x] or [y]. *)

Lemma path_link_1_converse:
  forall w,
  path link w y ->
  path F w x \/ path F w y.
Proof.
  (* One could prove that this statement is a consequence of
     [is_equiv_per_add_edge], but it seems more straightforward
     to perform a direct analysis. *)
  induction 1 using rtclosure_ind_l; intros.
  { eauto with rtclosure. }
  { unfold link, union, per_single in *. branches; unpack; subst.
    { forwards: IHrtclosure; eauto. branches; eauto with rtclosure. }
    { eauto with rtclosure. }}
Qed.

(* If a path from [w] to [z] exists after the link, and [z] is not [y], then
   this path existed before the link. *)

Lemma path_link_2_converse:
  forall w z,
  path link w z ->
  z <> y ->
  path F w z.
Proof.
  (* One could prove that this statement is a consequence of
     [is_equiv_per_add_edge], but it seems more straightforward
     to perform a direct analysis. *)
  unfold link, union, per_single.
  (* This takes care of the easy cases. *)
  induction 1 using rtclosure_ind_l; intros; repeat branches; unpack; subst; eauto with rtclosure.
  (* This is the interesting case, where the path of interest
     begins with an edge of [x] to [y]. Because [y] is a root,
     this path must stop there, so we must have [y = y']. This
     yields a contradiction. *)
  false. forwards: a_path_out_of_a_root_is_trivial; eauto.
Qed.

(* The descendants of [y] after the link are the former descendants of [x] and
   [y]. *)

Lemma descendants_link_1:
  descendants link y =
  descendants F x \u descendants F y.
Proof.
  unfold descendants. eapply set_ext. intro. rew_set in *. split; intro.
  { eauto using path_link_1_converse. }
  { intuition eauto using path_link_1, path_link_2. }
Qed.

(* If [z] is other than [y], then the descendants of [z] after the link are
   its descendants before the link. *)

Lemma descendants_link_2:
  forall z,
  z <> y ->
  descendants link z =
  descendants F z.
Proof.
  unfold descendants. intros.
  eapply set_ext. intro. rew_set in *. split; intro.
  { eauto using path_link_2_converse. }
  { eauto using path_link_2. }
Qed.

(* The set of descendants of a vertex [v] can only grow during a link. *)

Lemma descendants_link_2_incl:
  forall z,
  descendants F z \c descendants link z.
Proof.
  (* The proof is redundant with the proof of the previous lemma, but
     never mind. *)
  unfold descendants. intros. eapply incl_prove. intros. rew_set in *.
  eauto using path_link_2.
Qed.

(* The number of descendants of a vertex [v] can only grow during a link. *)

Lemma card_descendants_link_2_le:
  forall z,
  finite D ->
  card (descendants F z) <= card (descendants link z).
Proof.
  intros.
  eapply card_le_of_incl.
    { eauto using finite_descendants, is_dsf_link. }
    { eauto using descendants_link_2_incl. }
Qed.

End Link.

Hint Resolve is_root_link is_root_link_converse : is_root.

Ltac by_cases_on_link :=
  match goal with
  h: link ?F ?x ?y ?v ?w |- _ =>
    unfold link, union, per_single in h; branches; unpack; subst;
    repeat rewrite fupdate_neq
      by eauto using a_root_has_no_parent_disequality, edges_have_distinct_endpoints;
    repeat rewrite fupdate_eq
      by eauto
  end.

(* -------------------------------------------------------------------------- *)

(* If one wishes to reason in terms of the function [R], which maps every
   vertex to its representative, here is how the effect of a link operation
   is described. *)

Definition link_R V (R : V -> V) x y :=
  fun t => If R t = R x then y else R t.

(* The agreement between [R] and [is_repr F] is preserved when one
   applies [link_R] and [link] to [R] and [F], respectively. *)

Lemma link_R_link_agree:
  forall V (D : set V) R F x y,
  is_dsf D F ->
  fun_in_rel R (is_repr F) ->
  x \in D ->
  y \in D ->
  is_root F x ->
  is_root F y ->
  x <> y ->
  fun_in_rel
    (link_R R x y)
    (is_repr (link F x y)).
Proof.
  intros. intro w.
  assert (R x = x). { eauto using is_root_R_self. }
  assert (R y = y). { eauto using is_root_R_self. }
  unfold link_R. cases_if; unpack.
  (* Case: [w] is equivalent to [x]. *)
  { eapply is_repr_link_1; eauto.
    eapply is_repr_is_equiv_is_repr; eauto using is_root_is_repr.
    eauto using same_R_incl_is_equiv. }
  (* Case: [w] is not equivalent to [x]. *)
  { eapply is_repr_link_2; eauto.
    congruence. }
Qed.

