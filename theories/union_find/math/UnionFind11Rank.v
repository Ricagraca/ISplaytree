Set Implicit Arguments.
From TLC Require Import LibTactics LibLogic LibProd LibContainer LibSet
     LibRelation LibPer.
Local Notation path := rtclosure.
From iris_time.union_find.math Require Import TLCBuffer LibNatExtra
     UnionFind01Data.

(* -------------------------------------------------------------------------- *)

(* We now introduce ranks. *)

Section Rank.

Variable V : Type.
Variable D : set V.
Variable F : binary V.

(* We assume every vertex has a rank: that is, there is a total function of
   vertices to ranks. *)

Variable K : V -> nat.

(* If there is an edge from [x] to [y], then the rank of [x] should be less
   than the rank of [y]. In other words, the rank of a vertex is always less
   than the rank of its parent. *)

Definition rank_increases_along_edges :=
  forall x y, F x y -> K x < K y.

(* If [r] is a root of rank [k], then the number of its descendants (including
   itself) is at least [2^k]. This implies that, if the total number of vertices
   in the domain [D] is [N], then [k] is bounded by [log N], i.e., ranks are
   logarithmic. *)

Definition numerous_family :=
  forall r, is_root F r ->
  2^(K r) <= card (descendants F r).

(* For technical reasons, we must keep track of the fact that the domain [D]
   is finite. This means that the cardinal of this set, and the cardinals of
   its subsets, are natural numbers, and enjoy the usual properties of
   cardinals. *)

(* We also keep track of the fact that the rank is zero outside [D]. This
   allows not to update [K] when a new vertex is added, which is quite
   convenient. *)

(* A ranked disjoint set forest is a disjoint set forest that satisfies
   the additional properties about ranks that we have listed above. *)

Definition is_rdsf :=
  is_dsf D F /\
  rank_increases_along_edges /\
  numerous_family /\
  finite D /\
  (forall x, x \notin D -> K x = 0).

(* -------------------------------------------------------------------------- *)

(* In the following, we assume that [F] is a ranked disjoint set forest with
   domain [D] and ranks [K]. *)

Hypothesis is_rdsf_F:
  is_rdsf.

Definition is_rdsf_is_dsf := proj51 is_rdsf_F.
Definition is_rdsf_numerous_family := proj53 is_rdsf_F.
Definition is_rdsf_finite := proj54 is_rdsf_F.
Definition is_rdsf_zero_rank_outside_domain := proj55 is_rdsf_F.

Hint Resolve is_rdsf_is_dsf : core.

Hint Resolve is_rdsf_finite : finite.

(* -------------------------------------------------------------------------- *)

(* Every parent of nonzero rank. *)

Lemma parent_has_nonzero_rank:
  forall x y,
  F x y ->
  0 < K y.
Proof using is_rdsf_F.
  intros. assert (K x < K y). { eapply is_rdsf_F. eauto. } lia.
Qed.

(* Because rank increases along edges, if there is a path of length [k] from
   [x] to [y], then [K x + k <= K y] holds. *)

Lemma rank_bounds_height_precise:
  forall k x y,
  kpath F k x y ->
  K x + k <= K y.
Proof using is_rdsf_F.
  induction 1 as [| y x z ].
  lia.
  assert (K x < K y). { eapply is_rdsf_F. eauto. } lia.
Qed.

(* The rank of a vertex is an upper bound on its height in the forest. That is,
   a path that leads to a vertex [y] has length at most [K y]. In the absence
   of path compression, we could actually require an equality. *)

Lemma rank_bounds_height:
  forall k x y,
  kpath F k x y ->
  k <= K y.
Proof using D is_rdsf_F.
  intros. forwards: rank_bounds_height_precise; eauto. lia.
Qed.

(* Rank increases along a path. *)

Lemma rank_increases_along_a_path:
  forall x y,
  path F x y ->
  K x <= K y.
Proof using D is_rdsf_F.
  intros.
  forwards (?&?): rtclosure_kpath. eauto.
  forwards: rank_bounds_height_precise; eauto.
  lia.
Qed.

Lemma ancestor_has_greater_rank:
  forall x y,
  y \in ancestors F x ->
  K x <= K y.
Proof using D is_rdsf_F.
  unfold ancestors. intros. rew_set in *. eauto using rank_increases_along_a_path.
Qed.

(* Rank increases strictly along a nontrivial path. *)

Lemma rank_increases_strictly_along_a_nontrivial_path:
  forall x y,
  tclosure F x y ->
  K x < K y.
Proof using D is_rdsf_F.
  intros.
  forwards: tclosure_kpath. eauto. unpack.
  forwards: rank_bounds_height_precise. eauto.
  lia.
Qed.

(* Rank is logarithmic. *)

Lemma rank_is_logarithmic:
  forall x,
  x \in D ->
  K x <= log2 (card D).
Proof using is_rdsf_F.
  intros.
  (* First, we prove that this holds for every root. *)
  assert (f: forall x, is_root F x -> x \in D -> K x <= log2 (card D)).
  { intros. eapply prove_le_log2.
    eapply Nat.le_trans. eapply is_rdsf_numerous_family; eauto.
    (* card (descendants F x) <= card D *)
    eapply card_le_of_incl. eauto with finite.
    (* descendants F x \c D *)
    eapply descendants_subset_D; eauto. }
  (* Now, this holds for other vertices as well. *)
  intros.
  forwards (r&?&?): is_dsf_defined_is_repr x. eauto.
  transitivity (K r); eauto using rank_increases_along_a_path with sticky.
Qed.

(* The length of every path is logarithmic. *)

Lemma height_is_logarithmic:
  forall k x y,
  kpath F k x y ->
  k <= log2 (card D).
Proof using is_rdsf_F.
  introv h.
  tests: (y \in D).
  { eapply Nat.le_trans.
    eapply rank_bounds_height; eauto.
    eapply rank_is_logarithmic; eauto. }
  { forwards: only_trivial_paths_outside_D; eauto.
    lia. }
Qed.

(* Every rank is less than [card D]. This is not a precise bound, but it
   is sometimes useful. *)

Lemma rank_is_linear:
  forall x,
  x \in D ->
  K x < card D.
Proof using is_rdsf_F.
  intros.
  eapply Nat.le_lt_trans.
    { eapply rank_is_logarithmic. eauto. }
    { applys log2_lt_n. forwards~: card_ge_one D x. eauto with finite. }
Qed.

End Rank.

Hint Resolve is_rdsf_is_dsf : is_dsf.

Hint Unfold is_rdsf : is_rdsf.

Hint Resolve is_rdsf_finite : finite.

Hint Resolve is_rdsf_zero_rank_outside_domain : zero_rank.
