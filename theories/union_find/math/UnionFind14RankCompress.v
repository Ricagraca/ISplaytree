Set Implicit Arguments.
From TLC Require Import LibTactics LibLogic LibProd LibContainer LibSet
     LibRelation LibPer.
Local Notation path := rtclosure.
From iris_time.union_find.math Require Import LibNatExtra TLCBuffer
     UnionFind01Data UnionFind04Compress UnionFind05IteratedCompression
     UnionFind11Rank.

(* Compression in the presence of ranks. *)

(* -------------------------------------------------------------------------- *)

Section Compression.

Variable V : Type.
Variable D : set V.
Variable F : binary V.
Variable K : V -> nat.

(* Path compression preserves [is_rdsf]. *)

Lemma is_rdsf_compress:
  forall x y z,
  is_rdsf D F K ->
  F x y ->
  path F y z ->
  is_rdsf D (compress F x z) K.
Proof using.
  unfold is_rdsf. intros. unpack. splits.

  (* The disjoint set forest is preserved. *)
  { eauto using is_dsf_compress. }

  (* Rank increases along edges. *)
  { intros v w ?. by_cases_on_compress.
    (* Subcase: a pre-existing edge of [v] to [w]. The goal holds because
       the ranks of [v] and [w] have not changed. *)
    { eauto. }
    (* Subcase: the new edge of [x] to [z]. The goal holds because there
       was a nontrivial path of [x] to [z]. *)
    { eapply rank_increases_strictly_along_a_nontrivial_path.
      eauto 6 with is_rdsf. applys* tclosure_of_rtclosure_r. }}

  (* Numerous family. *)
  { intros r ?.
    erewrite compress_preserves_descendants_of_roots by eauto.
    eauto using compress_preserves_roots_converse. }

  (* Finite domain. *)
  { eauto. }

  (* Rank is zero outside domain. *)
  { eauto. }

Qed.

End Compression.

(* ------------------------------------------ ------------------------------- *)

(* Iterative path compression is a composition of several path compression
   steps, so it preserves [is_rdsf]. This property is easy to establish for
   [fw_ipc], and is then transported to [bw_ipc]. *)

Lemma is_rdsf_fw_ipc:
  forall V F x l F' D K,
  @fw_ipc V F x l F' ->
  is_rdsf D F K ->
  x \in D ->
  is_rdsf D F' K.
Proof using.
  induction 1; eauto 7 using is_rdsf_compress, is_repr_path with confined is_dsf.
Qed.

Lemma is_rdsf_bw_ipc:
  forall V F x l F' D K,
  @bw_ipc V F x l F' ->
  is_rdsf D F K ->
  x \in D ->
  is_rdsf D F' K.
Proof using.
  eauto using is_rdsf_fw_ipc, bw_ipc_fw_ipc with is_dsf.
Qed.

