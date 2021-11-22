Set Implicit Arguments.
From TLC Require Import LibTactics LibLogic LibFun LibProd LibContainer LibSet
     LibRelation LibPer.
Local Notation path := rtclosure.
From iris_time.union_find.math Require Import LibNatExtra TLCBuffer
     UnionFind01Data UnionFind03Link UnionFind11Rank.

(* Linking by rank. *)

(** TEMPORARY migration *)

Ltac by_cases_on_fupdate ::=
  rewrite fupdate_eq; case_if; subst.


(* -------------------------------------------------------------------------- *)

Section LinkByRank.

Variable V : Type.
Variable D : set V.
Variable F : binary V.
Variable K : V -> nat.

(* Linking by rank means that a link must be established from [x] to [y]
   if [x] has lower rank, and from [y] to [x] otherwise. If [x] and [y]
   have the same rank, then an arbitrary choice can be made, and the rank
   of the new root must be increased by one. *)

Definition link_by_rank_F (x y : V) :=
  If K x < K y then
    link F x y
  else
    link F y x.

Definition link_by_rank_K (x y : V) :=
  If K x = K y then
    fupdate K x (1 + K x)
  else
    K.

(* -------------------------------------------------------------------------- *)

(* Linking cannot cause a rank to decrease. *)

Lemma link_cannot_decrease_rank:
  forall x y v,
  K v <= link_by_rank_K x y v.
Proof using.
  unfold link_by_rank_K. intros. cases_if.
    { by_cases_on_fupdate; lia. }
    { lia. }
Qed.

(* Linking preserves the ranks of non-roots. *)

Lemma link_preserves_rank_of_non_roots:
  forall x y v,
  is_root F x ->
  ~ is_root F v ->
  K v = link_by_rank_K x y v.
Proof using.
  unfold link_by_rank_K. intros.
  (* The only case where the rank of [v] might change is when [x] and [y]
     have the same rank and [v] is [x]. But [x] is a root, and [v] is not
     a root, so this case cannot arise. *)
 cases_if; [ | reflexivity ].
 by_cases_on_fupdate. eauto.
Qed.

(* Linking by rank preserves [is_rdsf]. *)

Lemma is_rdsf_link:
  forall x y,
  is_rdsf D F K ->
  x \in D ->
  y \in D ->
  is_root F x ->
  is_root F y ->
  x <> y ->
  is_rdsf D (link_by_rank_F x y) (link_by_rank_K x y).
Proof using.
  unfold is_rdsf. introv (?&hRIAE&hNF&hFD&hZR). intros. splits.

  (* The disjoint set forest is preserved. *)
  { unfold link_by_rank_F. cases_if; eauto using is_dsf_link. }

  (* Rank increases along edges. *)
  { unfold link_by_rank_F, link_by_rank_K. intros v w ?.
    three_ways (K x) (K y).
    (* Case [K x = K y]. The link is from [y] to [x]. *)
    { by_cases_on_link.
      forwards: hRIAE. eassumption.
      (* Subcase: a pre-existing edge of [v] to [w]. The goal holds when [w]
         is [x] because the rank of [x] has increased (which is harmless).
         The goal holds when [w] is not [x] because nothing has changed. *)
      { case_if; subst; lia. }
      (* Subcase: the new edge of [y] to [x]. The goal holds because the
         rank of [x] has increased (which was necessary in this case). *)
      { case_if; subst; lia. }
    }
    (* Case [K x < K y]. No rank has changed, and the new link, from [x] to
       [y], respects the existing ranks. *)
    { by_cases_on_link; eauto. }
    (* Case [K x > K y]. Symmetric. *)
    { by_cases_on_link; eauto with lia. }
  }

  (* Numerous family. *)
  { unfold link_by_rank_F, link_by_rank_K. intros r ?.
    three_ways (K x) (K y).
    (* Case [K x = K y]. The link is from [y] to [x]. *)
    { by_cases_on_fupdate.
      (* Subcase: [r = x]. The rank of [x] has increased by one, so we
         have to prove that [x] has at least [2 * 2^(K x)] descendants.
         This works because the descendants of [x] now include the
         former descendants of [y]. *)
      { simpl.
        erewrite descendants_link_1 by eauto.
        rewrite card_disjoint_union by eauto using finite_descendants, disjoint_descendants.
        forwards hdx: hNF x. eauto.
        forwards hdy: hNF y. eauto.
        match goal with h: K x = K y |- _ => rewrite h in * end.
        lia. }
      (* Subcase: [r <> x]. The rank of [r] is unchanged, and its
         descendants are unchanged as well. *)
      { erewrite descendants_link_2 by eauto.
        eauto using is_root_link_converse. }}
    (* Case [K x < K y]. No rank has changed, and every vertex has at least
       as many descendants as before the link, so the goal holds. *)
    { transitivity (card (descendants F r)).
        eauto using is_root_link_converse.
        eauto using card_descendants_link_2_le. }
    (* Case [K x > K y]. Same argument. *)
    { transitivity (card (descendants F r)).
        eauto using is_root_link_converse.
        eauto using card_descendants_link_2_le. }
  }

  (* Finite domain. *)
  { eauto. }

  (* Rank is zero outside domain. *)
  { intros z ?.
    unfold link_by_rank_K. cases_if.
    { by_cases_on_fupdate. eauto. }
    { eauto. }
  }

Qed.

(* The effect of the new link on [dsf_per] is to fuse the equivalence classes
   of [x] and [y]. *)

Lemma dsf_per_add_edge_by_rank:
  forall x y,
  is_rdsf D F K ->
  x \in D ->
  y \in D ->
  is_root F x ->
  is_root F y ->
  x <> y ->
  dsf_per D (link_by_rank_F x y) =
  per_add_edge (dsf_per D F) x y.
Proof using.
  intros. unfold link_by_rank_F. cases_if;
  rewrite dsf_per_add_edge by eauto with is_dsf.
  { reflexivity. }
  { eapply per_add_edge_symmetric. }
Qed.

End LinkByRank.

(* -------------------------------------------------------------------------- *)

(* If one wishes to reason in terms of the function [R], which maps every
   vertex to its representative, here is how to describe linking by rank. *)

(* The new representative. *)

Definition new_repr_by_rank V K (x y : V) :=
  If K x < K y then y else x.

(* The new [R] is obtained by updating [R] with the new representative.
   We update the classes of both [x] and [y], so as to obtain a symmetric
   formulation. (Thus, we do not build on [link_R].) [z] stands for the
   new representative. *)

Definition link_by_rank_R V R (x y z : V) :=
  fun t => If R t = R x \/ R t = R y
  then z
  else R t.

(* Because [link_by_rank_R] was not defined in terms of [link_R], we must
   prove an explicit connection with [link_R]. *)

Lemma link_by_rank_R_case_1:
  forall V R K (x y : V),
  R y = y ->
  K x < K y ->
  link_by_rank_R R x y (new_repr_by_rank K x y) = link_R R x y.
Proof using.
  extens. intros w.
  unfold link_by_rank_R, new_repr_by_rank, link_R.
  cases_if; unpack.
  { branches; do 2 cases_if; congruence. }
  { cases_if; tauto. }
Qed.

Lemma link_by_rank_R_case_2:
  forall V R K (x y : V),
  R x = x ->
  ~ K x < K y ->
  link_by_rank_R R x y (new_repr_by_rank K x y) = link_R R y x.
Proof using.
  extens. intros w.
  unfold link_by_rank_R, new_repr_by_rank, link_R.
  cases_if; unpack.
  { branches; do 2 cases_if; congruence. }
  { cases_if; tauto. }
Qed.

(* The agreement between [R] and [is_repr F] is preserved when one applies
   [link_by_rank_R] and [link_by_rank_F] to [R] and [F], respectively. *)

Lemma link_by_rank_R_link_by_rank_F_agree:
  forall V (D : set V) R F K x y,
  is_rdsf D F K ->
  fun_in_rel R (is_repr F) ->
  x \in D ->
  y \in D ->
  is_root F x ->
  is_root F y ->
  x <> y ->
  fun_in_rel
    (link_by_rank_R R x y (new_repr_by_rank K x y) )
    (is_repr (link_by_rank_F F K x y)).
Proof using.
  intros.
  assert (R x = x). { eauto using is_root_R_self with is_dsf. }
  assert (R y = y). { eauto using is_root_R_self with is_dsf. }
  unfold link_by_rank_F. cases_if.
  (* Case: [K x < K y]. *)
  { rewrite link_by_rank_R_case_1 by eauto.
    eauto using link_R_link_agree with is_dsf. }
  (* Case: [K x >= K y]. *)
  { rewrite link_by_rank_R_case_2 by eauto.
    eauto using link_R_link_agree with is_dsf. }
Qed.

