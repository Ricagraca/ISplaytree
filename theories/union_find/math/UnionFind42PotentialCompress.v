Set Implicit Arguments.
From TLC Require Import LibTactics LibLogic LibProd LibContainer LibSet
     LibRelation LibPer LibMonoid.
Local Notation path := rtclosure.
From iris_time.union_find.math Require Import LibNatExtra LibIter InverseNatNat
     Ackermann InverseAckermann MiscArith TLCBuffer UnionFind01Data
     UnionFind03Link UnionFind04Compress UnionFind11Rank UnionFind21Parent
     UnionFind22ParentEvolution UnionFind41Potential.

Section BasicEvolution.

Variable r : nat.
Hypothesis r_geq_1: 1 <= r.

Notation prek := (prek r).
Notation k := (k r).
Notation i := (i r).
Notation rankr := (rankr r).

Variable V : Type.
Variable D : set V.
Variable F : binary V.
Variable K : V -> nat.
Hypothesis is_rdsf_F : is_rdsf D F K.

(* -------------------------------------------------------------------------- *)

(* During a compression, the function [k] is unchanged at ancestors of [y]. *)

Lemma compress_preserves_k_above_y:
  forall x y z,
  F x y ->
  path F y z ->
  forall v,
  path F y v ->
  ~ is_root F v ->
  k (compress F x z) K v = k F K v.
Proof using is_rdsf_F.
  unfold k, prek. intros.
  assert (x <> v).
  { eapply paths_have_distinct_endpoints; eauto with is_dsf tclosure. }
  erewrite compress_does_not_change_parent_of_v; eauto with is_dsf.
Qed.


(* -------------------------------------------------------------------------- *)

Section KxKy.

Notation is_root := (is_root F).
Notation path := (path F).
Notation p := (p F).
Notation prek := (prek F K).
Notation k := (k F K).
Notation i := (i F K).
Notation rankr := (rankr K).

(* Assume [x] and [y] are non-roots. (This is required for their level and index
   to be defined.) Assume that there is a non-trivial path from [x] to [y].
   Finally, assume that [x] and [y] have the same level, i.e., [k x = k y].
   Then, [iter (1 + i x) (A (prek x)) (rankr x)] is at most [rankr (p y)]. This
   is part of the proof of Lemma 4.10 in Alstrup et al.'s paper. *)

Lemma kx_ky:
  forall x y,
  ~ is_root x ->
  ~ is_root y ->
  path (p x) y ->
  k x = k y ->
  iter (1 + i x) (A (prek x)) (rankr x) <= rankr (p y).
Proof using is_rdsf_F r_geq_1.
  intros.
  assert (pp: prek x = prek y).
  { unfold k in *. lia. }
  (* Because there is a path from the parent of [x] to [y], the rank of [y]
     is at least the rank of the parent of [x]. *)
  assert (hxy: rankr (p x) <= rankr y).
  { eauto using rankr_increases_along_a_path. }
  (* By definition of [i], iterating [i x] times [A (prek x)], starting
     from [rankr x], takes us at most to [rankr (p x)]. *)
  assert (hx: iter (i x) (A (prek x)) (rankr x) <= rankr (p x)).
  { i f_betaf. }
  (* By definition of [prek], applying [A (prek x)] to [rankr y] takes us
     at least to [rankr (p y)]. *)
  assert (hy: A (prek x) (rankr y) <= rankr (p y)).
  { rewrite pp. k betaf_spec_direct. }
  (* Together, the above inequalities imply that iterating [1 + i x] times
     [A (prek x)], starting from [rankr x], takes us at most to [rankr (p y)].
     Which is our goal. *)
  simpl. rewrite hx. rewrite hxy. rewrite hy. eauto.
Qed.

End KxKy.

(* Under the same hypotheses as the previous lemma, if one performs path
   compression by installing an edge from [x] to its representative [z],
   then either [rankr x] changes (which means it increases, really, but we
   have not yet proved that), or [i x] increases. *)

Lemma kx_ky_compress:
  forall x y,
  ~ is_root F x ->
  ~ is_root F y ->
  path F (p F x) y ->
  k F K x = k F K y ->
  forall z,
  is_repr F x z ->
  k F K x = k (compress F x z) K x ->
  1 + i F K x <= i (compress F x z) K x.
Proof using is_rdsf_F r_geq_1.
  (* This proof is part of Lemma 4.10 in Alstrup et al.s paper, where
     it is really quite cryptic. Fortunately, it follows the same pattern
     as in Tarjan's proof. *)
  introv ? ? ? hkxy ? hkk.
  (* Because there is a path from [x] to the parent of [y], the
     representative of the parent of [y] must be [z]. This implies
     an inequality between the ranks of these vertices. *)
  assert (pyz: is_repr F (p F y) z).
  { eauto 11 using is_equiv_trans, is_equiv_parent, path_is_equiv with is_repr is_dsf. }
  destruct pyz.
  assert (rpyz: rankr K (p F y) <= rankr K z).
  { eauto using rankr_increases_along_a_path. }
  (* Now, recall the inequality which we proved previously. *)
  Opaque plus.
  forwards f: kx_ky x y; eauto.
  (* Combine the two inequalities. *)
  rewrite rpyz in f. clear rpyz.
  (* Note that [z] is the new parent of [x]. *)
  forwards w: compress_changes_parent_of_x_to_z x z; eauto.
  rewrite <- w in f by eauto. clear w.
  (* Massage. *)
  assert (prehkk: prek F K x = prek (compress F x z) K x).
  { unfold k in hkk. lia. }
  rewrite prehkk in f. clear prehkk.
  (* The assertion [f] guarantees that [i x] in the new state is
     at least [1 + i x] in the old state. *)
  i betaf_spec_reciprocal. (* tchac! *)
Qed.

End BasicEvolution.
