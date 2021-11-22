(* code taken from the Iris tutorial… *)

From iris.program_logic Require Import adequacy.
From iris_time.heap_lang Require Import proofmode notation.
From iris_time Require Import TimeCredits Reduction.

(** A function that sums all elements of a list, defined as a heap-lang value: *)
Definition sum_list : val :=
  rec: "sum_list" "l" :=
    match: "l" with
      NONE => #0
    | SOME "p" =>
      let: "x" := Fst !"p" in
      let: "l" := Snd !"p" in
      "x" + "sum_list" "l"
    end.

(** Representation predicate in separation logic for a list of integers [l]: *)
Fixpoint is_list `{heapGS Σ} (l : list Z) (v : val) : iProp Σ :=
  match l with
  | [] => ⌜ v = NONEV ⌝
  | x :: l' => ∃ (p : loc), ⌜ v = SOMEV #p ⌝ ∗
                 ∃ (v' : val), p ↦ (#x, v') ∗ is_list l' v'
  end%I.
(* [is_list_tr l v] means that the translation of [v] represents [l]: *)
Fixpoint is_list_tr `{timeCreditHeapG Σ} (l : list Z) (v : val) : iProp Σ :=
  match l with
  | [] => ⌜ v = NONEV ⌝
  | x :: l' => ∃ (p : loc), ⌜ v = SOMEV #p ⌝ ∗
                 ∃ (v' : val), p ↦ (#x, «v'») ∗ is_list_tr l' v'
  end%I.
(* some proofs: *)
Lemma is_list_translation `{!timeCreditHeapG Σ} l v :
  is_list l v -∗ is_list l v ∗ ⌜v = «v»%V⌝.
Proof.
  iIntros "Hl".
  destruct l as [|x l] ; simpl.
  - by iDestruct "Hl" as %->.
  - iDestruct "Hl" as (p) "[-> ?]".
    iSplitL.
    + iExists p. by iFrame.
    + done.
Qed.
Lemma is_list_tr_translation `{!timeCreditHeapG Σ} l v :
  is_list_tr l v -∗ is_list_tr l v ∗ ⌜v = «v»%V⌝.
Proof.
  iIntros "Hl".
  destruct l as [|x l] ; simpl.
  - by iDestruct "Hl" as %->.
  - iDestruct "Hl" as (p) "[-> Hl]" ; iDestruct "Hl" as (v') "[Hp Hl']".
    iSplitL.
    + iExists p. iSplit ; first done. eauto with iFrame.
    + done.
Qed.
Lemma is_list_tr_is_list_translation `{!timeCreditHeapG Σ} l v :
  is_list_tr l v ⊣⊢ is_list l «v»%V.
Proof.
  iSplit ; iIntros "Hl".
{
  iInduction l as [|x l] "IH" forall (v) ; simpl.
  - iDestruct "Hl" as %->.
    done.
  - iDestruct "Hl" as (p) "[-> Hl]" ; iDestruct "Hl" as (v) "[Hp Hl]".
    iPoseProof ("IH" with "Hl") as "Hl". eauto with iFrame.
}
{
  iInduction l as [|x l] "IH" forall (v) ; simpl.
  - iDestruct "Hl" as %Eq. iPureIntro. by eapply translationV_injective.
  - iDestruct "Hl" as (p) "[Eq Hl]" ; iDestruct "Eq" as %Eq ; iDestruct "Hl" as (v') "[Hp Hl]".
    change (InjRV #p)%V with «InjRV #p»%V in Eq. apply translationV_injective in Eq as ->.
    iDestruct (is_list_translation with "Hl") as "[Hl ->]".
    iPoseProof ("IH" with "Hl") as "Hl". eauto with iFrame.
}
Qed.
Lemma is_list_is_list_tr `{!timeCreditHeapG Σ} l v :
  (is_list l v ⊣⊢ is_list_tr l v)%I.
Proof.
  iSplit ; iIntros "Hl".
{
  iInduction l as [|x l] "IH" forall (v) ; simpl.
  - done.
  - iDestruct "Hl" as (p) "[-> Hl]" ; iDestruct "Hl" as (v) "[Hp Hl]".
    iExists p. iSplitR ; first done. iExists v.
    iDestruct (is_list_translation with "Hl") as "[Hl <-]".
    iFrame.
    iApply ("IH" with "Hl").
}
{
  iInduction l as [|x l] "IH" forall (v) ; simpl.
  - done.
  - iDestruct "Hl" as (p) "[-> Hl]" ; iDestruct "Hl" as (v) "[Hp Hl]".
    iExists p. iSplitR ; first done. iExists v.
    iDestruct (is_list_tr_translation with "Hl") as "[Hl <-]".
    iFrame.
    iApply ("IH" with "Hl").
}
Qed.

Definition sum_list_coq (l : list Z) : Z :=
  fold_right Z.add 0 l.

(** The proof using induction over [l]: *)
Lemma sum_list_spec `{!heapGS Σ} (l : list Z) (v : val) :
  {{{ is_list l v }}} sum_list v {{{ RET #(sum_list_coq l) ; is_list l v }}}.
Proof.
  iIntros (Φ) "Hl Post".
  iInduction l as [|x l] "IH" forall (v Φ) ; simpl.
  - iDestruct "Hl" as %->.
    wp_rec.
    wp_match.
    by iApply "Post".
  - iDestruct "Hl" as (p) "[-> Hl]". iDestruct "Hl" as (v) "[Hp Hl]".
    wp_rec.
    wp_match.
    wp_load. wp_proj. wp_let.
    wp_load. wp_proj. wp_let.
    wp_apply ("IH" with "Hl"). iIntros "Hl".
    wp_op.
    iApply "Post". eauto with iFrame.
Qed.
Lemma sum_list_translation_spec `{!timeCreditHeapG Σ} (l : list Z) (v : val) :
  TC_invariant -∗
  {{{ is_list_tr l v ∗ TC (4 + 13 * length l) }}} « sum_list v » {{{ RET #(sum_list_coq l) ; is_list_tr l v }}}.
Proof.
  iIntros "#Htickinv !#" (Φ) "[Hl Htc] Post".
  iInduction l as [|x l] "IH" forall (v Φ).
  - simpl.
    iDestruct "Hl" as %->.
    wp_tick_rec. wp_tick_match.
    by iApply "Post".
  - replace (4 + 13 * length (x :: l))%nat with (17 + 13 * length l)%nat by (simpl ; lia).
    iDestruct "Hl" as (p) "[-> Hl]" ; iDestruct "Hl" as (v) "[Hp Hl]".
    wp_tick_rec. wp_tick_match.
    wp_tick_load. wp_tick_proj. wp_tick_let.
    wp_tick_load. wp_tick_proj. wp_tick_let.
    iDestruct "Htc" as "[Htc1 Htc]".
    wp_apply ("IH" with "Hl Htc"). iIntros "Hl".
    wp_tick_op.
    iApply "Post". simpl. eauto with iFrame.
Qed.

Definition make_list : val :=
  rec: "make_list" "n" :=
    if: "n" = #0 then
      NONE
    else
      SOME (ref ("n", "make_list" ("n" - #1))).

Fixpoint make_list_coq (n : nat) : list Z :=
  match n with
  | 0%nat => []
  | S n'  => Z.of_nat n :: make_list_coq n'
  end.

(** The proof using induction over [l]: *)
Lemma make_list_spec `{!heapGS Σ} (n : nat) :
  {{{ True }}} make_list #n {{{ v, RET v ; is_list (make_list_coq n) v }}}.
Proof.
  iIntros (Φ) "_ Post".
  iInduction n as [|n'] "IH" forall (Φ) ; simpl.
  - wp_rec. wp_op. wp_if. wp_inj.
    by iApply "Post".
  - wp_rec. wp_op. wp_if.
    wp_op.
    assert (Z.of_nat n' = Z.of_nat (S n') - 1) as Eq by lia ; simpl in Eq ; destruct Eq.
    wp_apply "IH". iIntros (v') "Hl".
    change (Z.pos $ Pos.of_succ_nat n') with (Z.of_nat $ S n').
    wp_alloc p. wp_inj.
    iApply "Post". eauto with iFrame.
Qed.
Lemma make_list_translation_spec `{!timeCreditHeapG Σ} (n : nat) :
  TC_invariant -∗
  {{{ TC (4+7*n) }}} «make_list #n» {{{ v', RET v' ; is_list (make_list_coq n) v' }}}.
Proof.
  iIntros "#Htickinv !#" (Φ) "Htc Post".
  iInduction n as [|n'] "IH" forall (Φ).
  - wp_tick_rec. wp_tick_op. wp_tick_if. wp_tick_inj.
    by iApply "Post".
  - replace (4 + 7 * S n')%nat with (11 + 7 * n')%nat by lia.
    wp_tick_rec. wp_tick_op. wp_tick_if.
    wp_tick_op.
    assert (Z.of_nat n' = Z.of_nat (S n') - 1) as Eq by lia ; simpl in Eq ; destruct Eq.
    iDestruct "Htc" as "[? [? [? Htc]]]".
    wp_apply ("IH" with "Htc"). iIntros (v') "Hl".
    change (Z.pos $ Pos.of_succ_nat n') with (Z.of_nat $ S n').
    wp_tick_pair. wp_tick_alloc p. wp_tick_inj.
    iApply "Post". simpl. eauto with iFrame.
Qed.

Definition prgm (n : nat) : expr :=
  sum_list (make_list #n).

Lemma length_make_list_coq (n : nat) :
  length (make_list_coq n) = n.
Proof.
  induction n as [|n' IH].
  - done.
  - simpl. by f_equal.
Qed.

Lemma sum_list_coq_make_list_coq (n : nat) :
  sum_list_coq (make_list_coq n) = (Z.of_nat n * (Z.of_nat n + 1)) `div` 2.
Proof.
  rewrite - Z.div2_div.
  assert (2 * sum_list_coq (make_list_coq n) = (Z.of_nat n * (Z.of_nat n + 1))) as Eq.
  {
  induction n as [|n' IH].
  - done.
  - rewrite /= Z.mul_add_distr_l IH. lia.
  }
  assert (Zeven (Z.of_nat n * (Z.of_nat n + 1))) as Heven % Zeven_div2.
  {
    pose proof (Zeven_odd_dec n) as [ Heven | Hodd ].
    - by apply Zeven_mult_Zeven_l.
    - by apply Zeven_mult_Zeven_r, Zodd_plus_Zodd.
  }
  lia.
Qed.

Lemma prgm_spec `{!heapGS Σ} (n : nat) :
  {{{ True }}} prgm n {{{ v, RET v ; ⌜v = #(n*(n+1)/2)⌝ }}}.
Proof.
  iIntros (Φ) "_ Post".
  unfold prgm.
  wp_apply (make_list_spec with "[//]"). iIntros (v) "Hl".
  wp_apply (sum_list_spec with "Hl"). iIntros "Hl".
  iApply ("Post" with "[%]"). repeat f_equal. apply sum_list_coq_make_list_coq.
Qed.
Lemma prgm_translation_spec `{!timeCreditHeapG Σ} (n : nat) :
  TC_invariant -∗
  {{{ TC (8+20*n) }}} «prgm n» {{{ v, RET v ; ⌜v = #(n*(n+1)/2)⌝ }}}.
Proof.
  iIntros "#Htickinv !#" (Φ) "Htc Post".
  replace (8+20*n)%nat with ((4+7*n) + (4+13*n))%nat by lia ;
  rewrite TC_plus ; iDestruct "Htc" as "[Htc_make Htc_sum]".
  unfold prgm. simpl_trans.
  wp_apply (make_list_translation_spec with "Htickinv Htc_make"). iIntros (v) "Hl".
  iDestruct (is_list_translation with "Hl") as "[Hl ->]".
  wp_apply (sum_list_translation_spec with "Htickinv [Hl Htc_sum]"). {
    rewrite - is_list_tr_is_list_translation.
    erewrite length_make_list_coq. iFrame.
  } iIntros "Hl".
  iApply ("Post" with "[%]"). repeat f_equal. apply sum_list_coq_make_list_coq.
Qed.

Lemma prgm_timed_spec (n : nat) (σ : state) `{!timeCreditHeapPreG Σ} :
    adequate NotStuck (prgm n) σ (λ v _, v = #(n*(n+1)/2))
  ∧ bounded_time (prgm n) σ (8 + 20 * n)%nat.
Proof.
  apply (spec_tctranslation__adequate_and_bounded' (Σ:=Σ)).
  - by intros _ ->.
  - intros HtcHeapG. apply prgm_translation_spec.
  - assumption.
Qed.
