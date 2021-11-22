Set Implicit Arguments.
From TLC Require Import LibTactics LibLogic LibFun LibProd LibContainer
     LibSet LibRelation LibPer LibMonoid.
Local Notation path := rtclosure.
From iris_time.union_find.math Require Import LibNatExtra LibIter InverseNatNat
     Ackermann InverseAckermann MiscArith TLCBuffer
     UnionFind01Data UnionFind03Link UnionFind04Compress
     UnionFind05IteratedCompression UnionFind11Rank UnionFind13RankLink
     UnionFind14RankCompress UnionFind21Parent UnionFind22ParentEvolution
     UnionFind23Evolution UnionFind24Pleasant UnionFind41Potential
     UnionFind42PotentialCompress.

(* -------------------------------------------------------------------------- *)

(* We now study how level, index, and potential evolve over time. *)

(* -------------------------------------------------------------------------- *)

Section R.

Variable r : nat.
Hypothesis r_geq_1: 1 <= r.

Notation alphar := (alphar r).
Notation rankr := (rankr r).
Notation prek := (prek r).
Notation k := (k r).
Notation i := (i r).
Notation phi := (phi r).
Notation Phi := (Phi r).

Section StudyOfEvolution.

Variable  V    : Type.
Variable  D    : set V.
Variables F F' : binary V.
Variables K K' : V -> nat.

Hypothesis is_rdsf_F : is_rdsf D F K.
Hypothesis ev  : evolution D F K F' K'.

(* -------------------------------------------------------------------------- *)

Section NonRoot.

(* Now, let us study a vertex [v], which we assume already has a parent. *)

Variable v : V.
Hypothesis v_has_a_parent: ~ is_root F v.

(* -------------------------------------------------------------------------- *)

(* [rankr v] remains constant. *)

Lemma non_root_has_constant_rankr:
  rankr K v = rankr K' v.
Proof using ev v_has_a_parent.
  unfold rankr.
  forwards: non_root_has_constant_rank; eauto.
Qed.

(* [rankr (p v)] grows. *)

Lemma rankrpv_grows:
  rankr K (p F v) <= rankr K' (p F' v).
Proof using is_rdsf_F ev v_has_a_parent.
  unfold rankr. eapply plus_le_plus.
  eauto using Kpv_grows.
Qed.

(* -------------------------------------------------------------------------- *)

(* Because [rankr v] is constant while [rankr (p v)] may grow, [k v] can only
   grow. *)

Lemma kv_grows:
  k F K v <= k F' K' v.
Proof using is_rdsf_F ev v_has_a_parent r_geq_1.
  unfold k, prek, defk.
  eapply plus_le_plus.
  forwards f: non_root_has_constant_rankr; eauto.
  rewrite <- f.
  eapply betaf_monotonic; eauto using rankrpv_grows with k monotonic.
Qed.

(* -------------------------------------------------------------------------- *)

(* As long as [k v] remains constant, [i v] can only grow. *)

Lemma iv_grows_if_kv_constant:
  k F K v = k F' K' v ->
  i F K v <= i F' K' v.
Proof using is_rdsf_F ev v_has_a_parent.
  clear r_geq_1.
  introv h. unfold i.
  assert (h': prek F K v = prek F' K' v). { unfold k in h. lia. }
  rewrite <- h'.
  forwards f: non_root_has_constant_rankr; eauto.
  rewrite <- f.
  eapply betaf_monotonic; eauto using rankrpv_grows with i.
Qed.

(* -------------------------------------------------------------------------- *)

(* The potential of [v] cannot increase. (Lemma 4.5 on pages 18-19.) *)

Lemma phiv_cannot_increase_nonroot:
  phi F' K' v <= phi F K v.
Proof using is_rdsf_F ev v_has_a_parent r_geq_1.
  intros.
  assert (hK: rankr K v = rankr K' v). { eauto using non_root_has_constant_rankr. }
  assert (hR: ~ is_root F' v). { eauto using non_root_forever. }
  (* For [phi F K v], we are in case 2 or 3. *)
  tests hc : (alphar (rankr K v) = alphar (rankr K (p F v))).
  (* Case 2. *)
  { forwards hphi: phi_case_2 F; eauto. rewrite hphi. clear hphi.
    (* For [phi F' K' v], we are in case 2 or 3. *)
    tests hc' : (alphar (rankr K' v) = alphar (rankr K' (p F' v))).
    (* Case 2. *)
    (* This is the non-trivial case. *)
    { forwards hphi: phi_case_2 F'; eauto. rewrite hphi. clear hphi.
      eapply plus_le_plus.
      rewrite <- hK.
      eapply lexpo_cannot_increase.
      { eauto using i_le_rank. }
      { eauto using kv_grows. }
      { rewrite hK. rewrite hc'. eauto using k_lt_alphar, is_rdsf_evolution. }
      { exact iv_grows_if_kv_constant. }
    }
    (* Case 3. Immediate, since the new potential (i.e., the left-hand side of
       the inequality) is zero. *)
    { forwards hphi: phi_case_3 F'; eauto. rewrite hphi. clear hphi.
      lia. }
  }
  (* Case 3. *)
  { forwards hphi: phi_case_3 F; eauto. rewrite hphi. clear hphi.
    forwards: alphar_rankr_grows_along_edges_corollary; eauto.
    (* For [phi F' K' v], we must be in case 3 too. *)
    assert (alphar (rankr K' v) < alphar (rankr K' (p F' v))).
    { rewrite <- hK.
      eapply Nat.lt_le_trans. eauto.
      eapply alphar_monotonic. eauto. eauto using rankrpv_grows. }
    rewrite phi_case_3 by solve [ eauto | lia ].
    (* Thus, the potential was zero and remains zero. *)
    eauto.
  }
Qed.

End NonRoot.

(* -------------------------------------------------------------------------- *)

(* Let [v] be an arbitrary vertex (possibly a root). If its rank is preserved,
   then its potential cannot increase. *)

Lemma phiv_cannot_increase:
  forall v,
  rankr K v = rankr K' v ->
  phi F' K' v <= phi F K v.
Proof using is_rdsf_F ev r_geq_1.
  introv h. tests : (is_root F v).
  { (* Case: [v] is a root. The fact that the rank of [v] does not change
       is sufficient to prove that its potential cannot increase. *)
    rewrite (@phi_case_1 _ _ F K) by assumption.
    rewrite phi_upper_bound.
    rewrite h.
    eauto. }
  { (* Case: [v] is not a root. *)
    eauto using phiv_cannot_increase_nonroot. }
Qed.

End StudyOfEvolution.

(* -------------------------------------------------------------------------- *)

(* The increase of the potential [Phi] during a link is at most 2. This is
   Lemma 4.7 on page 19. The formal proof follows roughly the paper proof,
   except we find it necessary to make certain case analyses explicit. *)

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
  (* The following hypothesis is redundant, but it is convenient to require it. *)
  evolution D F K (link F x y) K' ->
  (* The conclusion. *)
  Phi D (link F x y) K' <= Phi D F K + 2.

Proof using r_geq_1.
  intros. unfold Phi.

  (* Either the rank of [y] remains the same, or it increases by one,
     and in that case, [x] and [y] initially have the same rank. We
     fully distinguish these two cases, as the first one is trivial. *)
  branches; unpack.

  (* Case: the rank of [y] is unchanged. In fact, every rank is unchanged. *)
  { subst K'.
    (* We do not even need the two-credit slack. *)
    match goal with |- ?a <= ?a' + _ => cut (a <= a'); [ lia | ] end.
    (* Every rank is unchanged, so no potential can increase. Easy. *)
    eapply fold_pointwise; eauto with finite typeclass_instances.
    eauto using phiv_cannot_increase.
  }

  (* Case: the rank of [y] is increased by one, and [x] and [y] initially have
     the same rank. Then, the potential of [y] may increase, but the potential
     of [x] decreases, and this compensates (up to a two-credit slack) for the
     increase in the potential of [y]. *)

  assert (hKx: rankr K x = rankr K y).
  { unfold rankr. lia. }
  assert (hK'y: rankr K' y = rankr K y + 1).
  { unfold rankr. subst K'. rewrite fupdate_eq by eauto. case_if; lia. }

  (* [is_rdsf] is preserved. Proving this is a bit painful, due to the way
     things are set up. We must do some house-keeping before we can apply
     the lemma [is_rdsf_link]. *)
  assert (is_rdsf D (link F x y) K').
  { assert (hF: link F x y = link_by_rank_F F K y x).
    { unfold link_by_rank_F. cases_if.
      false. unfold rankr in *. lia.
      reflexivity. }
    assert (hK: K' = link_by_rank_K K y x).
    { unfold link_by_rank_K. cases_if. eauto. }
    rewrite hF. rewrite hK.
    eauto using is_rdsf_link.
  }

  (* Set [y] and [x] aside. *)
  do 2 rewrite (@fold_isolate _ D y) by eauto with finite typeclass_instances.
  simpl.
  do 2 try rewrite (@fold_isolate _ (D \-- y) x);
   try solve [ eauto with finite typeclass_instances | rew_set in * ].
  simpl.
  (* Divide the goal into two subgoals. First, the total potential of all
     vertices other than [x] and [y] cannot increase. Second, the total
     potential of [x] and [y] increases by at most two. *)
  match goal with |- ?p + (?q + ?r) <= ?p' + (?q' + ?r') + ?a =>
    cut (r <= r' /\ p + q <= p' + q' + a); [ lia | split ]
  end.

  (* Subgoal 1: the vertices other than [x] and [y]. Again, their rank is
     unchanged, so their potential cannot increase. Easy. *)
  { eapply fold_pointwise; eauto with finite typeclass_instances. intros v ?.
    assert (rankr K v = rankr K' v).
    { unfold rankr. subst K'. rewrite fupdate_neq. auto. rew_set in *. tauto. }
    eauto using phiv_cannot_increase.
  }

  (* Subgoal 2: examine how the total potential of [x] and [y] evolves.
     This is the non-trivial part of this proof. *)

  (* The rank of [x] has not changed. *)
  assert (hK'x: rankr K x = rankr K' x).
  { subst K'. unfold rankr. rewrite fupdate_neq; eauto. }

  (* The parent of [x] is now [y]. *)
  forwards hpx: link_sets_parent F K x y; eauto using is_root_link.

  (* The (new) level and index of [x] are at least 1. *)
  assert (hkx: 1 <= k (link F x y) K' x).
  { unfold k. lia. }
  assert (hix: 1 <= i (link F x y) K' x).
  { eauto using i_ge_1, x_no_longer_a_root. }

  (* The vertex [y] is a root, both before and after the link. Thus, the potential
     of [y] before and after the link is as follows. *)
  forwards h: phi_case_1 r F K y; eauto. rewrite h. clear h.
  forwards h: phi_case_1 r (link F x y) K' y; eauto using is_root_link. rewrite h. clear h.

  (* The vertex [x] was a root before the link. Its potential before the link is as follows. *)
  forwards h: phi_case_1 r F K x; eauto. rewrite h. clear h.
  (* After the link, [x] is no longer a root. After the link, the rank of [x] is strictly
     less than the rank of [y]. Yet, we don't know whether the images of these ranks through
     [alphar] are equal or distinct. Thus, we don't know whether we are in case 2 or 3. A
     case analysis appears to be necessary; indeed, if we attempt to treat these two cases
     together, the fact that the subtraction of [i] is known to be safe only in case 2
     seems to become a problem. This case analysis does not explicitly appear in Alstrup et
     al.'s paper. *)
  tests hranks: (alphar (rankr K' x) = alphar (rankr K' y)).

  (* We are in case 2. The new potential of [x] is as follows. *)
  { forwards h: phi_case_2 r (link F x y) K' x; eauto using x_no_longer_a_root. congruence. rewrite h. clear h.
    (* The subtractions are safe. *)
    forwards: phi_case_2_safe_k r (link F x y) K' x; try rewrite hpx; eauto using x_no_longer_a_root.
    forwards: phi_case_2_safe_i r (link F x y) K' x; try rewrite hpx; eauto using x_no_longer_a_root.
    (* Simplify. *)
    rewrite <- hK'x in *. clear hK'x.
    rewrite hKx in *. clear hKx.
    rewrite hK'y in *. clear hK'y.
    rewrite <- hranks in *. clear hranks.
    (* Conclude via low-level arithmetic reasoning.
       We do not even need the two-credit slack in this case. *)
    eapply random_arithmetic_lemma_01; eauto.
  }

  (* We are in case 3. The new potential of [x] is zero. *)
  { forwards h: phi_case_3 r (link F x y) K' x; try rewrite hpx; eauto using x_no_longer_a_root. rewrite h. clear h.
    (* Simplify. *)
    rewrite <- hK'x in *. clear hK'x.
    rewrite hKx in *. clear hKx.
    rewrite hK'y in *. clear hK'y.
    (* Exploit [alphar (n + 1) <= alphar n + 1]. *)
    rewrite alphar_grows_one_by_one by eauto.
    (* Conclude via low-level arithmetic reasoning.
       This is where we need the two-credit slack. *)
    eapply random_arithmetic_lemma_02. eapply alphar_positive.
  }

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
  Phi D F' K' <= Phi D F K + 2.
Proof using r_geq_1.
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

(* The predicate [top_part] corresponds to the ``top part of the path''
   mentioned in the proof of Lemma 4.11. *)

Definition top_part V z F K (x : V) :=
  is_repr F x z /\
  alphar (rankr K x) = alphar (rankr K z).

Definition pleasant V z F K (x : V) :=
  pleasant (top_part z) (@k V) F K x.

Definition displeasure V z F K (x : V) :=
  displeasure (top_part z) (@k V) F K x.

(* The predicate [top_part] is hereditary. *)

Lemma top_part_hereditary:
  forall V D F K (x y z : V),
  @is_rdsf V D F K ->
  top_part z F K x ->
  F x y ->
  top_part z F K y.
Proof using r_geq_1.
  unfold top_part. intros. unpack.
  (* The representative of [y], the parent of [x], must be [z]. So, there
     is a path from [y] to [z]. *)
  assert (path F y z).
  { eauto using path_from_parent_to_repr_F with is_dsf. }
  split.
  { eauto using is_repr_is_root with is_repr. }
  (* Because [alphar . rankr] is constant all the way from [x] to [z],
     [x] and its parent have the same image through this function. *)
  assert (alphar (rankr K x) <= alphar (rankr K y)).
  { eauto using alphar_rankr_grows_along_a_path with rtclosure. }
  assert (alphar (rankr K y) <= alphar (rankr K z)).
  { eauto using alphar_rankr_grows_along_a_path. }
  lia.
Qed.

(* One step of path compression at [x] does not affect the ``top part
   of the path'' above [x]. *)

Lemma compress_preserves_top_part_above_y:
  forall V D F K x y z,
  @is_rdsf V D F K ->
  F x y ->
  path F y z ->
  forall v z',
  (* note: we allow [z'] and [z] to be distinct; this makes life easier down the road *)
  top_part z' F K v ->
  top_part z' (compress F x z) K v.
Proof using.
  unfold top_part. intros. unpack. split; eauto.
  { eauto using compress_preserves_is_repr_direct with is_dsf. }
Qed.

(* This result bounds the number of vertices in the top part of the path
   which are unpleasant (i.e., whose potential does not decrease). *)

(* The proof of Lemma 4.11 says this is a strict inequality. This is
   true. Here, we do not exploit the fact that a level is at least 1,
   which is why we end up establishing a large inequality. *)

Lemma bounded_displeasure_alstrup:
  forall V D F K,
  @is_rdsf V D F K ->
  forall x z,
  top_part z F K x ->
  displeasure z F K x <= alphar (rankr K z).
Proof using r_geq_1.
  intros.
  eapply bounded_displeasure_preliminary_2.
  { eauto. }
  { eauto using top_part_hereditary. }
  { intros y hTopLevel hNonRoot.
    (* There is an edge from [y] to its parent. *)
    forwards: parent_spec. eauto.
    (* The parent of [y] satisfies [top_part], too. Which implies
       that its [alphar . rankr] is equal to that of [z]. *)
    forwards [ ? hrpy ]: top_part_hereditary; eauto.
    rewrite <- hrpy. clear hrpy.
    (* The result follows. *)
    eauto using k_lt_alphar. }
  { assumption. }
Qed.

(* -------------------------------------------------------------------------- *)

(* During a path compression step at [x], the vertex [x] is the only one whose
   potential changes. So, if the potential of [x] decreases, then the total
   potential [Phi] decreases as well. *)

Lemma from_phi_to_Phi:
  forall V (D : set V) F K,
  is_rdsf D F K ->
  forall x z,
  ~ is_root F x ->
  is_repr F x z ->
  phi (compress F x z) K x < phi F K x ->
  Phi D (compress F x z) K < Phi D F K.
Proof using r_geq_1.
  intros.
  assert (x \in D).
  { eauto with confined is_dsf. }
  (* Set [x] aside. *)
  unfold Phi.
  do 2 rewrite (@fold_isolate _ D x) by eauto with finite typeclass_instances.
  simpl.
  (* Treat [x] on the one hand, and the other vertices on the other hand. *)
  match goal with |- ?p + ?q < ?p' + ?q' =>
    cut (p < p' /\ q <= q'); [ lia | split ]
  end.
  { assumption. }
  { eapply fold_pointwise; eauto with finite typeclass_instances.
    eauto using phiv_cannot_increase, compress_evolution, pleasant_non_root. }
Qed.

(* -------------------------------------------------------------------------- *)

(* If [alphar . rankr] is constant all the way from [x] to its root [z],
   then a pleasant path compression step at [x] causes the potential of
   [x] to decrease. This is Lemma 4.10 in Alstrup et al.'s paper. *)

Lemma pleasant_phi:
  forall V (D : set V) F K,
  is_rdsf D F K ->
  forall x z,
  pleasant z F K x ->
  is_repr F x z ->
  phi (compress F x z) K x < phi F K x.
Proof using r_geq_1.
  introv ? (hTopLevel & hNonRoot & hY) ?.
  destruct hTopLevel.
  destruct hY as [ y ? ]. unpack.
  (* The representative of the parent of [x] must be [z]. So, there is
     a path from the parent of [x] to [z]. *)
  assert (path F (p F x) z).
  { eauto using path_from_parent_to_repr. }
  (* Because [alphar . rankr] is constant all the way from [x] to [z],
     [x] and its parent have the same image through this function. *)
  assert (alphar (rankr K x) <= alphar (rankr K (p F x))).
  { eauto using alphar_rankr_grows_along_edges. }
  assert (alphar (rankr K (p F x)) <= alphar (rankr K z)).
  { eauto using alphar_rankr_grows_along_a_path. }
  assert (alphar (rankr K x) = alphar (rankr K (p F x))).
  { lia. }
  (* Hence, before compression, the potential of [x] is given by case 2. *)
  forwards h: phi_case_2 r F K x; eauto. rewrite h. clear h.
  (* No rank changes during compression. Hence, after compression, the
     potential of [x] is also given by case 2. *)
  assert (hxpx: alphar (rankr K x) = alphar (rankr K (p (compress F x z) x))).
  { erewrite compress_changes_parent_of_x_to_z by eauto. lia. }
  rewrite phi_case_2 by eauto using compress_preserves_roots_converse.
  (* Simplify, and apply a low-level arithmetic lemma. *)
  eapply plus_lt_plus.
  forwards: compress_evolution x; eauto.
  eapply lexpo_cannot_increase_and_decreases_if. (* yay! *)
  { eauto using i_le_rank. }
  { eauto using i_ge_1, is_rdsf_evolution, non_root_forever with lia. }
  { eauto using i_le_rank, is_rdsf_evolution, non_root_forever with lia. }
  { eauto using kv_grows. }
  { rewrite hxpx.
    eauto using k_lt_alphar, is_rdsf_evolution, non_root_forever with lia. }
  { eauto using iv_grows_if_kv_constant. }
  { eauto using prove_lexpo_decreases, kv_grows, kx_ky_compress. }
Qed.

(* During an arbitrary path compression step, the total potential [Phi] cannot
   increase. *)

Lemma arbitrary_Phi:
  forall V (D : set V) F K,
  is_rdsf D F K ->
  forall x y z,
  F x y ->
  path F y z ->
  Phi D (compress F x z) K <= Phi D F K.
Proof using r_geq_1.
  intros. unfold Phi.
  eapply fold_pointwise; eauto with finite typeclass_instances.
  eauto using phiv_cannot_increase with evolution.
Qed.

(* -------------------------------------------------------------------------- *)

(* We now evaluate the amortized cost of path compression in the ``top part''
   of the path. *)

Lemma amortized_cost_fw_ipc_top_part_inductive:
  forall V F x l F',
  @fw_ipc V F x l F' ->
  forall D K z,
  is_rdsf D F K ->
  top_part z F K x ->
  Phi D F' K + l <= Phi D F K + displeasure z F K x.
Proof using r_geq_1.
  unfold displeasure.
  induction 1; intros.

  (* FWIPCBase *)
  { lia. }

  (* FWIPCStep *)
  (* At this point, we unfortunately have two names for [z], so we must
     first argue that they are the same vertex. *)
  match goal with h: top_part ?z' _ _ _ |- _ =>
    assert (z' = z); [ destruct h | subst z' ]
  end.
  { eapply is_repr_is_equiv_is_repr_bis; eauto with is_dsf.
    eauto using path_is_equiv with rtclosure is_dsf. }

  (* Argue that compression does not affect the displeasure of [y]. This
     seems obvious, but is in fact non-trivial, as we must check that it
     affects neither the function [k] nor the predicate [top_part]. *)
  forwards: compress_preserves_displeasure_of_y (top_part z) x y z;
  eauto using is_repr_path, (@compress_preserves_k_above_y r),
              compress_preserves_top_part_above_y.

  (* Use the induction hypothesis. *)
  forwards: IHfw_ipc;
    eauto using is_rdsf_compress, is_repr_path,
                compress_preserves_top_part_above_y, top_part_hereditary.

  (* Now, perform case analysis. *)
  tests : (pleasant z F K x); unfold pleasant in *.

  { (* Case: [x] is pleasant. Then, path compression at [x] frees up one unit
       of potential, which pays for this step. The induction hypothesis does
       the rest. *)
    erewrite displeasure_parent_if_pleasant by eauto.
    forwards: from_phi_to_Phi x;
      eauto 8 using pleasant_phi, a_root_has_no_parent_contrapositive
               with is_dsf is_repr is_equiv.
    lia. }

  { (* Case: [x] is unpleasant. Then, we pay for this path compression step
       out of the [k] credits that we explicitly request from the client. *)
    erewrite displeasure_parent_if_unpleasant by eauto.
    forwards: arbitrary_Phi; eauto using is_repr_path.
    lia. }

Qed.

(* A corollary. *)

Lemma amortized_cost_fw_ipc_top_part:
  forall V D F K x z l F',
  @fw_ipc V F x l F' ->
  is_rdsf D F K ->
  top_part z F K x ->
  Phi D F' K + l <= Phi D F K + alphar (rankr K z).
Proof using r_geq_1.
  intros.
  rewrite amortized_cost_fw_ipc_top_part_inductive by eauto.
  rewrite bounded_displeasure_alstrup by eauto.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)

(* Say [x] is ``easy'' if [alphar . rankr] is NOT constant all the way from [x]
   to its root [z], but maps [x] and its parent to the same value. In this case,
   a path compression step at [x] causes the potential of [x] to decrease. This
   is Lemma 4.9 in Alstrup et al.'s paper. *)

Lemma easy_phi:
  forall V (D : set V) F K,
  is_rdsf D F K ->
  forall x,
  ~ is_root F x ->
  forall z,
  is_repr F x z ->
  alphar (rankr K x) = alphar (rankr K (p F x)) ->
  alphar (rankr K (p F x)) < alphar (rankr K z) ->
  phi (compress F x z) K x < phi F K x.
Proof using r_geq_1.
  intros.
  (* The representative of the parent of [x] must be [z]. So, there is
     a path from the parent of [x] to [z]. *)
  assert (path F (p F x) z).
  { eauto using path_from_parent_to_repr. }
  (* Before compression, the potential of [x] is given by case 2. Hence,
     it is non-zero. *)
  forwards h: phi_case_2_lower_bound r F K x; eauto.
  (* After compression, the parent of [x] is [z], so the potential of [x]
     is given by case 3. Hence, it is zero. *)
  assert (alphar (rankr K x) <> alphar (rankr K (p (compress F x z) x))).
  { erewrite compress_changes_parent_of_x_to_z by eauto. lia. }
  rewrite phi_case_3 by eauto using compress_preserves_roots_converse.
  (* The result follows. *)
  lia.
Qed.

(* -------------------------------------------------------------------------- *)

(* The following result covers the so-called ``bottom part'' of the path.
   It combines Lemma 4.8 and the ``bottom part'' of Lemma 4.10, and calls
   the previous result [amortized_cost_fw_ipc_top_part] when it reaches
   the ``top part'' of the path. *)

Lemma amortized_cost_fw_ipc_bottom_part:
  forall V F x l F',
  @fw_ipc V F x l F' ->
  forall D K z,
  is_rdsf D F K ->
  is_repr F x z ->
  Phi D F' K + l <= Phi D F K + 2 * alphar (rankr K z) - alphar (rankr K x).
Proof using r_geq_1.
  induction 1; intros.

  (* FWIPCBase *)
  {
    (* [x] is [z]. *)
    assert (x = z).
    { eauto using a_path_out_of_a_root_is_trivial, is_repr_path. }
    subst z.
    (* The result follows, quite trivially. *)
    lia.
  }

  (* FWIPCStep *)

  (* At this point, we unfortunately have two names for [z], so we must
     first argue that they are the same vertex. *)
  match goal with h: is_repr _ x ?z' |- _ =>
    assert (z' = z); [ | subst z' ]
  end.
  { eapply is_repr_is_equiv_is_repr_bis; eauto with is_dsf.
    eauto using path_is_equiv with rtclosure is_dsf. }

  (* The parent of [x] is [y]. *)
  assert (hpx: p F x = y).
  { eauto using parent_unique. }

  (* The function [alphar . rankr] grows along the path from [x] to [z]. *)
  assert (alphar (rankr K x) <= alphar (rankr K z)).
  { eauto using alphar_rankr_grows_along_a_path, is_repr_path. }

  (* Perform case analysis: are [x] and [z] at the same height? *)
  tests: (alphar (rankr K x) = alphar (rankr K z)).

  (* Case: yes, [x] and [z] are at the same height. This means [x] is in
     fact in the top part of the path. *)
  {
    assert (top_part z F K x).
    { split; eauto. }
    (* The previous analysis applies. *)
    forwards: amortized_cost_fw_ipc_top_part x; eauto with fw_ipc.
    (* The result follows. *)
    lia.
  }

  (* Case: no, [x] and [z] are at different heights. *)

  (* Use the induction hypothesis. *)
  forwards: IHfw_ipc;
    eauto using is_rdsf_compress, is_repr_path,
                compress_preserves_is_repr_direct with is_dsf.

  (* Perform case analysis: are [x] and its parent at the same height? *)
  tests: (alphar (rankr K x) = alphar (rankr K (p F x))).

  (* Case: [x] is easy. *)
  {
    (* Path compression at [x] frees up one unit of potential, which
       pays for this step. *)
    forwards: from_phi_to_Phi x;
      eauto 8 using easy_phi, a_root_has_no_parent_contrapositive with lia.
    rewrite hpx in *.
    lia.
  }

  (* Case: [x] is not easy. *)
  {
    forwards: arbitrary_Phi; eauto using is_repr_path.
    rewrite hpx in *.
    (* In that case, [alphar . rankr] at [y] is one more than at [x],
       which pays for this step. *)
    assert (alphar (rankr K x) <= alphar (rankr K y)).
    { eauto using alphar_rankr_grows_along_a_path with rtclosure. }
    lia.
  }

Qed.

(* As a corollary, we obtain the amortized cost of iterated path compression,
   in a formulation based on [fw_ipc]. *)

Lemma amortized_cost_fw_ipc:
  forall V F x l F',
  @fw_ipc V F x l F' ->
  forall D K z,
  is_rdsf D F K ->
  is_repr F x z ->
  Phi D F' K + l < Phi D F K + 2 * alphar (rankr K z).
Proof using r_geq_1.
  intros.
  forwards: amortized_cost_fw_ipc_bottom_part; eauto.
  assert (alphar (rankr K x) > 0). { eauto using alphar_positive. }
  assert (alphar (rankr K z) > 0). { eauto using alphar_positive. }
  lia.
Qed.

(* -------------------------------------------------------------------------- *)

(* This corollary combines [ipc_defined], [amortized_cost_fw_ipc], and
   [bw_ipc_fw_ipc], so as to obtain the amortized cost of iterated path
   compression, in a variant based on [bw_ipc], and in a form where the [ipc]
   predicate appears as part of the conclusion (not as a hypothesis). *)

(* PUBLIC *)
Lemma amortized_cost_of_iterated_path_compression_local:
  forall V D F K x,
  @is_rdsf V D F K ->
  x \in D ->
  exists l F' z,
  is_repr F x z /\
  bw_ipc F x l F' /\
  Phi D F' K + l < Phi D F K + 2 * alphar (rankr K z).
Proof using r_geq_1.
  intros.
  forwards (l&F'&?): ipc_defined x. eauto with is_dsf.
  forwards (z&?): is_dsf_defined_is_repr x. eauto with is_dsf.
  exists l F' z. splits;
  eauto using amortized_cost_fw_ipc, bw_ipc_fw_ipc with is_dsf.
Qed.

(* A simplified version, where we bound the rankr of [z] by the cardinality of
   [D], plus [r - 1]. *)

(* PUBLIC *)
Lemma amortized_cost_of_iterated_path_compression_global:
  forall V D F K x,
  @is_rdsf V D F K ->
  x \in D ->
  exists l F',
  bw_ipc F x l F' /\
  Phi D F' K + l < Phi D F K + 2 * alphar (card D + (r - 1)).
Proof using r_geq_1.
  intros.
  forwards (l&F'&z&?): amortized_cost_of_iterated_path_compression_local; eauto. unpack.
  exists l F'. splits; eauto.
  assert (K z <= log2 (card D)).
  { eapply rank_is_logarithmic;
    eauto 6 using is_equiv_in_D_direct, path_is_equiv, is_repr_path with is_dsf. }
  assert (1 <= card D).
  { eapply card_ge_one; eauto with finite. }
  assert (K z < card D).
  { forwards: log2_lt_n (card D); eauto. lia. }
  assert (rankr K z <= card D + (r - 1)).
  { unfold rankr. lia. }
  assert (alphar (rankr K z) <= alphar (card D + (r - 1))).
  { eapply alphar_monotonic; eauto. }
  lia.
Qed.

End R.

(* A further simplified version, where we take [r] to be 1. *)

(* PUBLIC *)
Lemma amortized_cost_of_iterated_path_compression_simplified:
  forall V D F K x,
  @is_rdsf V D F K ->
  x \in D ->
  exists l F',
  bw_ipc F x l F' /\
  Phi 1 D F' K + l <= Phi 1 D F K + 2 * alpha (card D) + 3.
Proof using.
  intros.
  forwards (l&F'&?&hb): amortized_cost_of_iterated_path_compression_global; eauto.
  exists l F'. splits; eauto.
  replace (card D + (1 - 1)) with (card D) in hb by lia.
  unfold alphar, prealphar, defalphar in hb.
  assert (f: alpha (card D + 1) <= alpha (card D) + 1).
  { eauto using alpha_grows_one_by_one. }
  lia.
Qed.
