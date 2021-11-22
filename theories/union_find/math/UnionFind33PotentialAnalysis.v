Set Implicit Arguments.
From TLC Require Import LibTactics LibLogic LibFun LibProd LibContainer
     LibSet LibRelation LibPer LibMonoid.
Local Notation path := rtclosure.
From iris_time.union_find.math Require Import LibNatExtra LibIter InverseNatNat
     Ackermann InverseAckermann MiscArith TLCBuffer
     UnionFind01Data UnionFind03Link UnionFind04Compress
     UnionFind05IteratedCompression UnionFind11Rank UnionFind13RankLink
     UnionFind14RankCompress UnionFind21Parent UnionFind22ParentEvolution
     UnionFind23Evolution UnionFind24Pleasant UnionFind31Potential
     UnionFind32PotentialCompress.

(* -------------------------------------------------------------------------- *)

(* We now study how level, index, and potential evolve over time. *)

(* The lemmas that are meant to be used by the client are marked PUBLIC. *)

(* -------------------------------------------------------------------------- *)

Section StudyOfEvolution.

Variable  V    : Type.
Variable  D    : set V.
Variables F F' : binary V.
Variables K K' : V -> nat.

Hypothesis is_rdsf_F : is_rdsf D F K.
Hypothesis ev  : evolution D F K F' K'.

(* -------------------------------------------------------------------------- *)

Section StudyOfV.

(* Now, let us study a vertex [v], which we assume already has a parent. *)

Variable v : V.
Hypothesis v_has_a_parent: ~ is_root F v.

(* -------------------------------------------------------------------------- *)

Section NonZeroRank.

(* Let us further assume that [v] has non-zero rank. This is required
   for [k] and [i] to be well-defined. *)

Hypothesis v_has_nonzero_rank: 0 < K v.

(* -------------------------------------------------------------------------- *)

(* Because [K v] is constant while [K (p v)] may grow, [k v] can only grow
   with time. *)

Lemma kv_grows:
  k F K v <= k F' K' v.
Proof using is_rdsf_F ev v_has_a_parent v_has_nonzero_rank.
  unfold k.
  forwards f: non_root_has_constant_rank; eauto.
  rewrite <- f.
  eapply betaf_monotonic; eauto using Kpv_grows with k monotonic.
Qed.

(* -------------------------------------------------------------------------- *)

(* As long as [k v] remains constant, [i v] can only grow. *)

Lemma iv_grows_if_kv_constant:
  k F K v = k F' K' v ->
  i F K v <= i F' K' v.
Proof using is_rdsf_F ev v_has_a_parent.
  introv h. unfold i.
  rewrite <- h.
  forwards f: non_root_has_constant_rank; eauto.
  rewrite <- f.
  eapply betaf_monotonic; eauto using Kpv_grows with i.
Qed.

(* -------------------------------------------------------------------------- *)

(* The potential of [v] cannot increase, and drops by at least one if either
   [k] or [i] changes. *)

Lemma phiv_cannot_increase_and_decreases_if:
  forall N,
  card D <= N ->
                                                 phi F' K' N v <= phi F K N v /\
  (k F K v < k F' K' v \/ i F K v < i F' K' v -> phi F' K' N v <  phi F K N v).
Proof using is_rdsf_F ev v_has_a_parent v_has_nonzero_rank.
  intros.
  assert (hK: K v = K' v). { eauto using non_root_has_constant_rank. }
  rewrite phi_case_2 by eauto using non_root_forever with lia.
  rewrite phi_case_2 by eauto.
  rewrite <- hK.
  eapply lexpo_cannot_increase_and_decreases_if.
    { eauto using i_le_rank. }
    { eauto using i_ge_1, is_rdsf_evolution, non_root_forever with lia. }
    { rewrite hK. eauto using i_le_rank, is_rdsf_evolution, non_root_forever with lia. }
    { eauto using kv_grows. }
    { eauto using k_lt_alpha, is_rdsf_evolution, non_root_forever with lia. }
    { eauto using iv_grows_if_kv_constant. }
Qed.

End NonZeroRank.

(* -------------------------------------------------------------------------- *)

(* (We are still under the assumption that [v] has a parent.) Regardless of
   the rank of [v], its potential cannot increase. *)

Lemma phiv_cannot_increase_if_v_has_a_parent:
  forall N,
  card D <= N ->
  phi F' K' N v <= phi F K N v.
Proof using is_rdsf_F ev v_has_a_parent.
  intros.
  tests : (0 < K v).
  (* If [v] has nonzero rank, the above lemma applies. *)
  {
  eapply phiv_cannot_increase_and_decreases_if; eauto. }
  (* If [v] has zero rank, then its initial and final potential are zero. *)
  forwards: non_root_has_constant_rank; eauto.
  do 2 (rewrite phi_case_1b by lia).
  reflexivity.
Qed.

End StudyOfV.

(* -------------------------------------------------------------------------- *)

(* Let [v] be an arbitrary vertex. If its rank is preserved, then its potential
   cannot increase. *)

Lemma phiv_cannot_increase:
  forall N,
  card D <= N ->
  forall v,
  K v = K' v ->
  phi F' K' N v <= phi F K N v.
Proof using is_rdsf_F ev.
  introv ? h. tests : (is_root F v).
  { (* Case: [v] is a root. The fact that the rank of [v] does not change
       is sufficient to prove that its potential cannot increase. *)
    rewrite (@phi_case_1a _ F K) by assumption.
    rewrite phi_upper_bound.
    rewrite h.
    eauto. }
  { (* Case: [v] is not a root. *)
    eauto using phiv_cannot_increase_if_v_has_a_parent. }
Qed.

End StudyOfEvolution.

(* -------------------------------------------------------------------------- *)

(* The increase of the potential [Phi] during a link is at most [alpha N]. The
   proof is routine: in short, during a link of [x] to [y], the only vertex
   whose potential can increase is [y], and its rank can increase at most by
   one, leading to an increase in potential of at most [alpha N]. *)

(* Note that [N] is the fixed, agreed-upon upper bound on the number vertices.
   It is not the current number [n] of vertices. *)

Lemma potential_increase_during_link_preliminary:
  forall V D F K K' (x y : V),
  is_rdsf D F K ->
  x <> y ->
  x \in D ->
  y \in D ->
  is_root F x ->
  is_root F y ->
  (* In this lemma, we consider only the following two cases. It is easy
     to later argue that, by symmetry, this covers all cases. *)
  K x < K y /\ K' = K \/
  K x = K y /\ K' = fupdate K y (1 + K y) ->
  (* The follomwing hypothesis is redundant, but it is convenient to require it. *)
  evolution D F K (link F x y) K' ->
  (* The conclusion. *)
  forall N,
  card D <= N ->
  Phi D (link F x y) K' N <= Phi D F K N + alpha N.
Proof using.
  intros. unfold Phi.
  (* The only vertex whose potential can increase is [y]. Set it aside. *)
  do 2 rewrite (@fold_isolate _ D y) by eauto with finite typeclass_instances.
  simpl.
  (* Treat [y] on the one hand, and the other vertices on the other hand. *)
  match goal with |- ?p + ?q <= ?p' + ?q' + ?a =>
    cut (p <= p' + a /\ q <= q'); [ lia | split ]
  end.
  (* Case: [y]. This vertex is a root, both before and after the link.
     There remains to argue that the rank of [y] increases by at most 1. *)
  { do 2 rewrite phi_case_1a by eauto using is_root_link.
    assert (f: K' y <= K y + 1).
    { branches; unpack; subst; try rewrite fupdate_eq by eauto; try case_if; lia. }
    rewrite f.
    ring_simplify. eauto. }
  { (* Case: some vertex [v] other than [y]. Because [v] is not [y], the rank of [v]
         does not change. Thus, its potential cannot increase. *)
    eapply fold_pointwise; eauto with finite typeclass_instances.
    intros v hv.
    rewrite in_remove_eq in hv.
    unfold notin in hv. rewrite in_single_eq in hv.
    unpack.
    assert (K v = K' v).
    { branches; unpack; subst; try rewrite fupdate_neq by assumption; eauto. }
    eauto using phiv_cannot_increase. }
Qed.

(* PUBLIC *)
Lemma potential_increase_during_link:
  forall V D F F' K K' (x y : V),
  is_rdsf D F K ->
  x <> y ->
  x \in D ->
  y \in D ->
  is_root F x ->
  is_root F y ->
  F' = link_by_rank_F F K x y ->
  K' = link_by_rank_K K x y ->
  forall N,
  card D <= N ->
  Phi D F' K' N <= Phi D F K N + alpha N.
Proof using.
  intros.
  assert (evolution D F K F' K').
  { subst. eauto with evolution. }
  subst.
  unfold link_by_rank_F, link_by_rank_K in *.
  three_ways (K x) (K y);
  eapply potential_increase_during_link_preliminary;
    eauto with lia.
Qed.

(* -------------------------------------------------------------------------- *)

(* Instantiate the theory of [UnionFind24Pleasant]. *)

Definition non_zero_rank V (F : binary V) (K : V -> nat) x :=
  0 < K x.

Definition pleasant V (F : binary V) (K : V -> nat) (x : V) :=
  pleasant (@non_zero_rank V) (@k V) F K x.

Definition displeasure V (F : binary V) (K : V -> nat) (x : V) :=
  displeasure (@non_zero_rank V) (@k V) F K x.

Lemma bounded_displeasure_tarjan:
  forall V D F K,
  @is_rdsf V D F K ->
  forall x,
  displeasure F K x <= alpha (card D) + 1.
Proof using.
  introv h. intros.
  eapply bounded_displeasure.
  { eauto. }
  { intros y z ? ?.
    assert (K y < K z). { eapply h. eauto. }
    unfold non_zero_rank.
    lia. }
  { intros. eapply k_lt_alpha; eauto. }
  { intros y z ? ? ?.
    assert (K y < K z). { eapply h. eauto. }
    unfold non_zero_rank.
    lia. }
Qed.

(* -------------------------------------------------------------------------- *)

(* A pleasant path compression step at [x] causes the potential of [x] to
   decrease. *)

Lemma pleasant_phi:
  forall V (D : set V) F K,
  is_rdsf D F K ->
  forall x,
  pleasant F K x ->
  forall z,
  is_repr F x z ->
  forall N,
  card D <= N ->
  phi (compress F x z) K N x < phi F K N x.
Proof using.
  unfold pleasant. intros.
  forwards: compress_evolution; eauto using pleasant_non_root.
  unfold UnionFind24Pleasant.pleasant in *. unpack.
  (* As per our previous analysis, it is sufficient to prove that either [k x]
     or [i x] has increased. *)
  eapply phiv_cannot_increase_and_decreases_if; eauto.
  (* Since we know that [k x] increases or remains unchanged, it suffices to
     prove that if [k x] remains unchanged, then [i x] increases. This follows
     from the lemma [kx_ky_compress]. *)
  eauto using prove_lexpo_decreases, kv_grows, kx_ky_compress with congruence.
Qed.

(* During a pleasant path compression step, the potential of the vertices
   other than [x] cannot increase, so the total potential [Phi] must
   decrease. *)

Lemma pleasant_Phi:
  forall V (D : set V) F K,
  is_rdsf D F K ->
  forall x,
  pleasant F K x ->
  forall z,
  is_repr F x z ->
  forall N,
  card D <= N ->
  Phi D (compress F x z) K N < Phi D F K N.
Proof using.
  unfold pleasant. intros.
  assert (x \in D).
  { unfold UnionFind24Pleasant.pleasant in *. unpack. eauto with confined is_dsf. }
  (* The only vertex whose potential decreases is [x]. Set it aside. *)
  unfold Phi.
  do 2 rewrite (@fold_isolate _ D x) by eauto with finite typeclass_instances.
  simpl.
  (* Treat [x] on the one hand, and the other vertices on the other hand. *)
  match goal with |- ?p + ?q < ?p' + ?q' =>
    cut (p < p' /\ q <= q'); [ lia | split ]
  end.
  { eauto using pleasant_phi. }
  { eapply fold_pointwise; eauto with finite typeclass_instances.
    eauto using phiv_cannot_increase, compress_evolution, pleasant_non_root. }
Qed.

(* During an arbitrary path compression step, the total potential [Phi] cannot
   increase. *)

Lemma unpleasant_Phi:
  forall V (D : set V) F K,
  is_rdsf D F K ->
  forall x y z,
  F x y ->
  path F y z ->
  forall N,
  card D <= N ->
  Phi D (compress F x z) K N <= Phi D F K N.
Proof using.
  intros. unfold Phi.
  eapply fold_pointwise; eauto with finite typeclass_instances.
  eauto using phiv_cannot_increase with evolution.
Qed.

(* -------------------------------------------------------------------------- *)

(* If there are [k] unpleasant non-root vertices among the ancestors of [x],
   then performing path compression along the path that begins at [x] has an
   amortized cost of [k]. That is, the initial potential, to which one adds
   [k] credits supplied by the user, is at least as high as the sum of the
   final potential and the actual cost [l], which is the length of the path. *)

Lemma amortized_cost_fw_ipc_preliminary:
  forall V F x l F',
  @fw_ipc V F x l F' ->
  forall D K,
  is_rdsf D F K ->
  forall N,
  card D <= N ->
  Phi D F' K N + l <= Phi D F K N + displeasure F K x.
Proof using.
  unfold displeasure.
  induction 1; intros.
  (* FWIPCBase *)
  { lia. }
  (* FWIPCStep *)
  { forwards: compress_preserves_displeasure_of_y (@non_zero_rank V) x y z;
    eauto using is_repr_path, compress_preserves_k_above_y.
    tests : (pleasant F K x); unfold pleasant in *.
    { (* Case: [x] is pleasant. Then, path compression at [x] frees up one unit
         of potential, which pays for this step. The induction hypothesis does
         the rest. *)
      erewrite displeasure_parent_if_pleasant by eauto.
      forwards: pleasant_Phi; eauto 8 with is_dsf is_repr is_equiv.
      forwards: IHfw_ipc; eauto using is_rdsf_compress, is_repr_path with lia. }
    { (* Case: [x] is unpleasant. Then, we pay for this path compression step
         out of the [k] credits that we explicitly request from the client. *)
      erewrite displeasure_parent_if_unpleasant by eauto.
      forwards: unpleasant_Phi; eauto using is_repr_path.
      forwards: IHfw_ipc; eauto using is_rdsf_compress, is_repr_path with lia. }
  }
Qed.

(* By plugging in an upper bound for [k], one obtains the following result,
   which describes the amortized complexity of iterative path compression. *)

(* The amortized cost of iterative path compression is [O(alpha n)], where [n]
   is the current number of vertices. One could in fact refine this bound
   to [O(alpha (log2 n))], but that is the same thing. *)

Lemma amortized_cost_fw_ipc:
  forall V D F K x l F' N,
  @fw_ipc V F x l F' ->
  is_rdsf D F K ->
  card D <= N ->
  Phi D F' K N + l <= Phi D F K N + alpha N + 1.
Proof using.
  (* Note: we could write [alpha (card D)] in the right-hand side
           instead of [card N]. *)
  introv ? ? hN.
  rewrite amortized_cost_fw_ipc_preliminary by eauto.
  rewrite bounded_displeasure_tarjan by eauto.
  rewrite hN.
  lia.
Qed.

(* This corollary combines [ipc_defined], [amortized_cost_fw_ipc],
   and [bw_ipc_fw_ipc]. *)

(* PUBLIC *)
Lemma amortized_cost_of_iterated_path_compression:
  forall V D F K x N,
  @is_rdsf V D F K ->
  x \in D ->
  card D <= N ->
  exists l F',
  bw_ipc F x l F' /\
  Phi D F' K N + l <= Phi D F K N + alpha N + 1.
Proof using.
  intros.
  forwards: ipc_defined. eauto with is_dsf. unpack.
  do 3 econstructor; eauto using amortized_cost_fw_ipc, bw_ipc_fw_ipc with is_dsf.
Qed.

