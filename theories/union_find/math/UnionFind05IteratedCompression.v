Set Implicit Arguments.
From TLC Require Import LibTactics LibLogic LibProd LibContainer LibSet
     LibRelation LibPer .
Local Notation path := rtclosure.
From iris_time.union_find.math Require Import TLCBuffer
     UnionFind01Data UnionFind04Compress.

(* We now define an inductive predicate that encodes the process of performing
   path compression iteratively along a path, up to the root. [ipc] stands for
   ``iterative path compression''. The predicate [ipc F x l F'] means that in
   the initial state [F], performing path compression along the path that
   begins at [x] leads in [l] steps to the final state [F']. *)

(* We define backward and forward variants of this predicate, [bw_ipc] and
   [fw_ipc].

   The forward variant corresponds intuitively to a two-pass algorithm, where
   the first pass finds the representative [z], and the second pass performs
   iterated path compression. This formulation is clearly the sequential
   composition of several path compression steps. For this reason, this
   formulation is more amenable to a simple proof of several lemmas (e.g.
   [amortized_cost_fw_ipc_preliminary] and [is_rdsf_fw_ipc]).

   The backward variant corresponds intuitively to the one-pass, recursive
   formulation of path compression, where path compression is performed as the
   stack is unwound. This formulation is *not* clearly the sequential
   composition of several path compression steps, because it is not obvious
   a priori that the representative of [x] before compression is the
   representative of [x] after compression.

   Naturally, the two predicates are in fact equivalent. *)

Inductive bw_ipc V (F : binary V) : V -> nat -> binary V -> Prop :=
| BWIPCBase:
    forall x,
    is_root F x ->
    bw_ipc F x 0 F
| BWIPCStep:
    forall F' F'' x y z l,
    F x y ->
    is_repr F y z ->
    bw_ipc F y l F' ->
    F'' = compress F' x z ->
    bw_ipc F x (S l) F''.

Inductive fw_ipc V : binary V -> V -> nat -> binary V -> Prop :=
| FWIPCBase:
    forall F x,
    is_root F x ->
    fw_ipc F x 0 F
| FWIPCStep:
    forall (F : binary V) F' x y z l,
    F x y ->
    is_repr F y z ->
    fw_ipc (compress F x z) y l F' ->
    fw_ipc F x (S l) F'.

Hint Constructors bw_ipc : bw_ipc.
Hint Constructors fw_ipc : fw_ipc.

(* ------------------------------------------ ------------------------------- *)

(* Provided there is no path from [y] to [x], forward iterative compression at
   [y] commutes with one step of compression at [x]. *)

(* This statement should really be presented as a commutative diagram. *)

Lemma fw_ipc_compress_preliminary:
  forall V F x y z l F',
  @fw_ipc V F y l F' ->
  ~ path F y x ->
  fw_ipc (compress F x z) y l (compress F' x z).
Proof using.
  induction 1; intros.
  (* Base. *)
  { econstructor;
    eauto using compress_preserves_roots_other_than_x, not_rtclosure_inv_neq. }
  (* Step. *)
  { forwards: IHfw_ipc.
    (* The assumption that there is no path from [y] to [x] remains true as we move
       from [y] to its successor and perform one step of compression at [y]. *)
    { eauto 6 using compress_preserves_paths_converse, is_repr_path with rtclosure. }
    (* The assumption that there is no path from [y] to [x] gives us the fact that
       [y] and [x] are distinct. It is used twice below. *)
    forwards: not_rtclosure_inv_neq; eauto.
    econstructor.
    { eauto using compress_preserves_other_edges. }
    { eauto using compress_preserves_is_repr_weak with rtclosure. }
    { rewrite compress_compress by eauto. assumption. }}
Qed.

(* A corollary of the previous lemma. *)

Lemma fw_ipc_compress:
  forall V D F x y z l F',
  @is_dsf V D F ->
  F x y ->
  is_repr F y z ->
  fw_ipc F y l F' ->
  fw_ipc (compress F x z) y l (compress F' x z).
Proof using.
  eauto using fw_ipc_compress_preliminary, acyclicity with tclosure.
Qed.

(* -------------------------------------------------------------------------- *)

(* Provided there is no path from [y] to [x], backward iterative compression at
   [y] commutes with one step of un-compression at [x]. *)

(* This statement should really be presented as a commutative diagram. *)

Lemma bw_ipc_compress_preliminary:
  forall V Fxz y l Fxz',
  @bw_ipc V Fxz y l Fxz' ->
  forall F x z,
  Fxz = compress F x z ->
  ~ path F y x ->
  exists F',
  Fxz' = compress F' x z /\
  bw_ipc F y l F'.
Proof using.
  induction 1; intros; subst.
  (* Base. *)
  { eexists. split. eauto.
    econstructor; eauto using compress_preserves_roots_converse. }
  (* Step. *)
  { (* The assumption that there is no path from [y] to [x] gives us the fact that
       [y] and [x] are distinct. *)
    forwards: not_rtclosure_inv_neq; eauto.
    (* This implies that the edge of [x] to [y], which exists after compression,
       already existed before compression. *)
    forwards: compress_preserves_other_edges_converse; eauto.
    forwards: IHbw_ipc.
      { eauto. }
      { eauto 6 using compress_preserves_paths_converse, is_repr_path with rtclosure. }
    unpack. subst. eexists. split.
    eapply compress_compress. { eauto. }
    econstructor;
      eauto 6 using compress_preserves_is_repr_weak_converse,
        compress_preserves_paths_converse, is_repr_path with rtclosure. }
Qed.

(* A corollary of the previous lemma. *)

Lemma bw_ipc_compress:
  forall V D F x y z l F'',
  @is_dsf V D F ->
  F x y ->
  is_repr F y z ->
  bw_ipc (compress F x z) y l F'' ->
  exists F',
  F'' = compress F' x z /\
  bw_ipc F y l F'.
Proof using.
  eauto using bw_ipc_compress_preliminary, acyclicity with tclosure.
Qed.

(* -------------------------------------------------------------------------- *)

(* Equivalence between [fw_ipc] and [bw_ipc]. *)

Lemma bw_ipc_fw_ipc:
  forall V F x l F',
  @bw_ipc V F x l F' ->
  forall D,
  is_dsf D F ->
  @fw_ipc V F x l F'.
Proof using.
  induction 1; intros; subst; econstructor; eauto using fw_ipc_compress.
Qed.

Lemma fw_ipc_bw_ipc:
  forall V F x l F',
  @fw_ipc V F x l F' ->
  forall D,
  is_dsf D F ->
  @bw_ipc V F x l F'.
Proof using.
  induction 1; intros; subst.
  { econstructor; eauto. }
  { forwards: IHfw_ipc.
      eauto using is_dsf_compress, is_repr_path.
    forwards: bw_ipc_compress; eauto. unpack.
    econstructor; eauto. }
Qed.

(* -------------------------------------------------------------------------- *)

(* Iterative path compression, starting at an arbitrary vertex [x], is always
   possible. *)

(* I believe that this lemma may be useful in avoiding a chicken-and-egg
   problem. In the CFML proof of the OCaml code for iterative path
   compression, we must prove that we have enough credits for the code to
   operate. This requires arguing that the initial potential is high enough,
   using the lemma [amortized_cost_fw_ipc]. But this lemma has a hypothesis of
   the form [fw_ipc V F x l F'] -- that is, it requires proving, ahead of
   time, that iterative path compression terminates. *)

Lemma ipc_defined_preliminary:
  forall V D F,
  @is_dsf V D F ->
  forall x r,
  path F x r ->
  is_root F r ->
  exists l F',
  bw_ipc F x l F'.
Proof using.
  induction 2 using rtclosure_ind_l; intros.
  { repeat econstructor. eauto. }
  { forwards: IHrtclosure. eauto. unpack.
    do 2 eexists. eapply BWIPCStep; eauto with is_repr. }
Qed.

Lemma ipc_defined:
  forall V D F,
  @is_dsf V D F ->
  forall x,
  exists l F',
  bw_ipc F x l F'.
Proof using.
  intros.
  forwards [ r [ ? ? ]]: is_dsf_defined_is_repr x. eauto.
  eauto using ipc_defined_preliminary.
Qed.

(* -------------------------------------------------------------------------- *)

(* Iterative path compression is a composition of several path compression
   steps, so it preserves the agreement between [R] and [F]. This property
   is easy to establish for [fw_ipc], and is then transported to [bw_ipc]. *)

Lemma fw_ipc_preserves_RF_agreement:
  forall V F x l F',
  @fw_ipc V F x l F' ->
  forall R D,
  is_dsf D F ->
  fun_in_rel R (is_repr F) ->
  fun_in_rel R (is_repr F').
Proof using.
  induction 1; eauto 6 using is_repr_path, is_dsf_compress, compress_R_compress_agree.
Qed.

Lemma bw_ipc_preserves_RF_agreement:
  forall V F x l F',
  @bw_ipc V F x l F' ->
  forall R D,
  is_dsf D F ->
  fun_in_rel R (is_repr F) ->
  fun_in_rel R (is_repr F').
Proof using.
  eauto using fw_ipc_preserves_RF_agreement, bw_ipc_fw_ipc.
Qed.

