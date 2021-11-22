Set Implicit Arguments.
From TLC Require Import LibTactics LibLogic LibFun LibProd LibContainer LibSet
     LibRelation LibPer LibMonoid.
Local Notation path := rtclosure.
From iris_time.union_find.math Require Import LibNatExtra LibIter
     InverseNatNat Ackermann InverseAckermann MiscArith TLCBuffer
     UnionFind01Data UnionFind03Link UnionFind04Compress
     UnionFind05IteratedCompression UnionFind11Rank UnionFind13RankLink
     UnionFind14RankCompress UnionFind21Parent UnionFind22ParentEvolution.

(* -------------------------------------------------------------------------- *)

(* We define a notion of evolution over time, which includes links and
   compressions, and study how parent and rank evolve over time. *)

Section Evolution.

Variable V : Type.

(* -------------------------------------------------------------------------- *)

(* The state evolves through links and compressions. This is encoded by the
   predicate [evolution D F K F' K']. *)

Inductive evolution (D : set V) : binary V -> (V -> nat) -> binary V -> (V -> nat) -> Prop :=
| EvLink:
    forall F K x y,
    x \in D ->
    y \in D ->
    is_root F x ->
    is_root F y ->
    x <> y ->
    evolution D F K
      (link_by_rank_F F K x y)
      (link_by_rank_K K x y)
| EvCompress:
    forall (F : binary V) K x y z,
    F x y ->
    path F y z ->
    evolution D F K
      (compress F x z)
      K.

End Evolution.

(* A path compression step that creates a direct edge from a non-root vertex
   [x] to its representative [z] is a valid evolution. *)

Lemma compress_evolution:
  forall V (D : set V) F K,
  is_rdsf D F K ->
  forall x,
  ~ is_root F x ->
  forall z,
  is_repr F x z ->
  evolution D F K (compress F x z) K.
Proof using.
  intros.
  assert (pxz: is_repr F (p F x) z).
  { eauto using is_repr_is_equiv_is_repr, is_equiv_parent with is_dsf. }
  destruct pxz.
  econstructor.
    { eapply (@parent_spec _ F). eauto. }
    { eauto. }
Qed.

(* -------------------------------------------------------------------------- *)

Section StudyOfEvolution.

Variable  V    : Type.
Variable  D    : set V.
Variables F F' : binary V.
Variables K K' : V -> nat.

Hypothesis is_rdsf_F : is_rdsf D F K.
Hypothesis ev  : evolution D F K F' K'.

(* -------------------------------------------------------------------------- *)

(* Evolution preserves [is_rdsf]. *)

Lemma is_rdsf_evolution:
  is_rdsf D F' K'.
Proof using is_rdsf_F ev.
  inversion ev; subst; eauto using is_rdsf_link, is_rdsf_compress.
Qed.

(* -------------------------------------------------------------------------- *)

(* The rank of every vertex grows with time. *)

Lemma rank_grows:
  forall v,
  K v <= K' v.
Proof using ev.
  clear is_rdsf_F.
  intros. inversion ev; subst; eauto using link_cannot_decrease_rank.
Qed.

(* -------------------------------------------------------------------------- *)

Section StudyOfV.

(* Now, let us study a vertex [v], which we assume already has a parent. *)

Variable v : V.
Hypothesis v_has_a_parent: ~ is_root F v.

(* -------------------------------------------------------------------------- *)

(* If [v] has a parent, [K v] remains constant. *)

Lemma non_root_has_constant_rank:
  K v = K' v.
Proof using ev v_has_a_parent.
  clear is_rdsf_F.
  inversion ev; subst; eauto using link_preserves_rank_of_non_roots.
Qed.

(* -------------------------------------------------------------------------- *)

(* If [v] has a parent, then this remains true forever. In other words,
   a non-root remains a non-root. *)

Lemma non_root_forever:
  ~ is_root F' v.
Proof using ev v_has_a_parent.
  clear is_rdsf_F.
  inversion ev; subst.
  (* Link. *)
  { unfold link_by_rank_F. cases_if; eauto using is_root_link_converse. }
  (* Compression. *)
  { eauto using compress_preserves_roots_converse. }
Qed.

(* -------------------------------------------------------------------------- *)

(* The quantity [K (p v)] grows with time, either because the rank of
   the parent of [v] changes (during a link), or because the parent
   of [v] changes (during a compression). *)

Lemma Kpv_grows:
  K (p F v) <= K' (p F' v).
Proof using is_rdsf_F ev v_has_a_parent.
  (* Let us distinguish two cases: either the parent of [v] has remained
     the same, or it has changed. *)
  tests : (p F v = p F' v).
  { (* If it has remained the same, then the result follows from the fact
       that the rank grows with time. *)
    match goal with h: _ = _ |- _ => rewrite h end.
    eauto using rank_grows. }
  { (* If it has changed: *)
    inversion ev; subst; clear ev.
    (* During a link, this means that [v] must be the source of the new
       edge. However, we have assume that [v] is not a root, so this
       case is impossible. *)
    { false.
      unfold link_by_rank_F, not in *.
      tests : (K x < K y); eauto using link_preserves_parent. }
    (* During a compression, this means that [v] must be [x], and we
       have replaced an edge of [x] to [y] with an edge of [x] to [z].
       Because there is a path of [y] to [z], the rank of [z] is greater
       than the rank of [y]. *)
    { forwards [ ? hz ]: compress_changes_parent_of_x_only; eauto.
      subst v. rewrite hz in *; clear hz.
      forwards hpx: parent_unique; eauto.
      rewrite hpx in *; clear hpx.
      eauto using rank_increases_along_a_path. }
  }
Qed.

End StudyOfV.

End StudyOfEvolution.

Hint Constructors evolution : evolution.

