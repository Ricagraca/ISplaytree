Set Implicit Arguments.
From TLC Require Import LibTactics LibLogic LibProd LibContainer LibSet
     LibRelation LibPer LibMonoid.
Local Notation path := rtclosure.
From iris_time.union_find.math Require Import LibNatExtra LibIter InverseNatNat
     Ackermann InverseAckermann MiscArith TLCBuffer
     UnionFind01Data UnionFind03Link UnionFind04Compress UnionFind11Rank
     UnionFind21Parent UnionFind22ParentEvolution UnionFind31Potential.

Section BasicEvolution.

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
  unfold k. intros.
  assert (x <> v).
  { eapply paths_have_distinct_endpoints; eauto with is_dsf tclosure. }
  erewrite compress_does_not_change_parent_of_v; eauto with is_dsf.
Qed.

(* -------------------------------------------------------------------------- *)

(* Assume [x] and [y] both have non-zero rank and both have a parent. Assume
   that there is a non-trivial path from [x] to [y]. Finally, assume that [x]
   and [y] have the same level, i.e., [k x = k y]. Write [kk] for this common
   level. Then, [iter (1 + i x) (A kk) (K x)] is at most [K (p y)]. This
   technical lemma appears in the last paragraph of Tarjan's course notes. *)

Lemma kx_ky:
  forall x y kk,
  0 < K x ->
  ~ is_root F x ->
  ~ is_root F y ->
  path F (p F x) y ->
  k F K x = kk ->
  k F K y = kk ->
  iter (1 + i F K x) (A kk) (K x) <= K (p F y).
Proof using is_rdsf_F.
  introv ? ? ? ? hkx hky.
  (* Because there is a path from the parent of [x] to [y], the rank of [y]
     is at least the rank of the parent of [x]. *)
  assert (hxy: K (p F x) <= K y). { eauto using rank_increases_along_a_path. }
  assert (0 < K y). { forwards: parent_has_greater_rank x; eauto. lia. }
  (* By definition of [i], iterating [i x] times [A kk], starting
     from [K x], takes us at most to [K (p x)]. *)
  assert (hx: iter (i F K x) (A kk) (K x) <= K (p F x)).
  { rewrite <- hkx. i f_betaf. }
  (* By definition of [k], applying [A kk] to [K y] takes us at
     least to [K (p y)]. Another way of seeing this would be say
     that the previous assertion holds for [y] too, and [i y] is
     at least 1. *)
  assert (hy: A kk (K y) <= K (p F y)).
  { rewrite <- hky. k betaf_spec_direct. }
  (* Together, the above inequalities imply that iterating [1 + i x] times
     [A kk], starting from [K x], takes us at most to [K (p y)]. Which is
     our goal. *)
  simpl. rewrite hx. rewrite hxy. rewrite hy. eauto.
Qed.

(* Under the same hypotheses as the previous lemma, if one performs path
   compression by installing an edge from [x] to its representative [z],
   then either [k x] changes (which means it increases, really, but we
   have not yet proved that), or [i x] increases. *)

Lemma kx_ky_compress:
  forall x y kk,
  0 < K x ->
  ~ is_root F x ->
  ~ is_root F y ->
  path F (p F x) y ->
  k F K x = kk ->
  k F K y = kk ->
  forall z,
  is_repr F x z ->
  k F K x = k (compress F x z) K x ->
  1 + i F K x <= i (compress F x z) K x.
Proof using is_rdsf_F.
  introv ? ? ? ? hkx hky ? hkk.
  (* Because there is a path from [x] to the parent of [y], the
     representative of the parent of [y] must be [z]. This implies
     an inequality between the ranks of these vertices. *)
  assert (pyz: is_repr F (p F y) z).
  { eauto 11 using is_equiv_trans, is_equiv_parent, path_is_equiv with is_repr is_dsf. }
      (* TEMPORARY: this is too slow! *)
  destruct pyz.
  assert (rpyz: K (p F y) <= K z).
  { eauto using rank_increases_along_a_path. }
  (* Now, recall the inequality which we proved previously. *)
  Opaque plus.
  forwards f: kx_ky x y kk; eauto.
  (* Combine the two inequalities. *)
  rewrite rpyz in f.
  (* Note that [z] is the new parent of [x]. *)
  forwards w: compress_changes_parent_of_x_to_z x z; eauto.
  rewrite <- w in f by eauto.
  (* Massage. *)
  rewrite <- hkx in f. rewrite hkk in f.
  (* The assertion [f] guarantees that [i x] in the new state is
     at least [1 + i x] in the old state. *)
  i betaf_spec_reciprocal. (* tchac! *)
Qed.

End BasicEvolution.

