From iris_time Require Import Base.
From iris.base_logic Require Import invariants.
From iris.algebra Require Import lib.gmap_view.
From iris.proofmode Require Import coq_tactics.
From iris_time.heap_lang Require Import proofmode notation adequacy lang.
From iris_time Require Import Auth_nat Reduction Tactics.
From iris_time Require Export Simulation.
Import uPred.

Implicit Type e : expr.
Implicit Type v : val.
Implicit Type σ : state.
Implicit Type t : list expr.
Implicit Type K : ectx heap_ectx_lang.
Implicit Type m n : nat.
Implicit Type φ ψ : val → Prop.
Implicit Type Σ : gFunctors.



(*
 * Abstract interface of time credits
 *)

(* Ideally, this would be represented as a record (or a typeclass), but it has
 * to be an Iris proposition (iProp Σ) and not a Coq proposition (Prop). *)
Definition TC_interface `{!irisGS heap_lang Σ, Tick}
  (TC : nat → iProp Σ)
: iProp Σ := (
    ⌜∀ n, Timeless (TC n)⌝
  ∗ (|==> TC 0%nat)
  ∗ ⌜∀ m n, TC (m + n)%nat ≡ (TC m ∗ TC n)⌝
  ∗ (∀ v, {{{ TC 1%nat }}} tick v {{{ RET v ; True }}})
)%I.



(*
 * Prerequisites on the global monoid Σ
 *)

Class timeCreditHeapPreG Σ := {
  timeCreditHeapPreG_heapPreG :> heapGpreS Σ ;
  timeCreditHeapPreG_inG :> inG Σ (authR natUR) ;
}.

Class timeCreditHeapG Σ := {
  timeCreditHeapG_heapG :> heapGS Σ ;
  timeCreditHeapG_inG :> inG Σ (authR natUR) ;
  timeCreditHeapG_loc :> TickCounter ;
  timeCreditHeapG_name : gname ;
}.

Local Notation γ := timeCreditHeapG_name.
Local Notation ℓ := tick_counter.



(*
 * Implementation and specification of `TC` and `tick`
 *)

(* This code is irrelevant for tick_spec but has to be unsafe for proving
 * the safety theorem: *)
Definition fail : val :=
  λ: <>, #() #().

Global Instance credits_tick {_:TickCounter} : Tick :=
  generic_tick fail.



Section TickSpec.

  Context `{timeCreditHeapG Σ}.

  Definition TC (n : nat) : iProp Σ :=
    own γ (◯nat n).

  (* Note: we can avoid the update modality by redefining TC like so:
         Definition TC' n : iProp Σ := ⌜n = 0%nat⌝ ∨ TC n. *)
  Lemma zero_TC :
    ⊢ |==> TC 0.
  Proof. apply own_unit. Qed.
  Lemma TC_plus m n :
    TC (m + n) ≡ (TC m ∗ TC n)%I.
  Proof. by rewrite /TC auth_frag_op own_op. Qed.
  Lemma TC_succ n :
    TC (S n) ≡ (TC 1%nat ∗ TC n)%I.
  Proof. by rewrite (eq_refl : S n = 1 + n)%nat TC_plus. Qed.
  Lemma TC_weaken (n₁ n₂ : nat) :
    (n₂ ≤ n₁)%nat →
    TC n₁ -∗ TC n₂.
  Proof. apply own_auth_nat_weaken. Qed.

  Lemma TC_timeless n :
    Timeless (TC n).
  Proof. exact _. Qed.

  (* We give higher priorities to the (+) instances so that the (S n)
     instances are not chosen when m is a constant. *)
  Global Instance into_sep_TC_plus m n : IntoSep (TC (m + n)) (TC m) (TC n) | 0.
  Proof. by rewrite /IntoSep TC_plus. Qed.
  Global Instance from_sep_TC_plus m n : FromSep (TC (m + n)) (TC m) (TC n) | 0.
  Proof. by rewrite /FromSep TC_plus. Qed.
  Global Instance into_sep_TC_succ n : IntoSep (TC (S n)) (TC 1) (TC n) | 100.
  Proof. by rewrite /IntoSep TC_succ. Qed.
  Global Instance from_sep_TC_succ n : FromSep (TC (S n)) (TC 1) (TC n) | 100.
  Proof. by rewrite /FromSep [TC (S n)] TC_succ. Qed.

  Definition timeCreditN := nroot .@ "timeCredit".

  Definition TC_invariant : iProp Σ :=
    inv timeCreditN (∃ (m:nat), ℓ ↦ #m ∗ own γ (●nat m))%I.

  Theorem tick_spec s E (v : val) :
    ↑timeCreditN ⊆ E →
    TC_invariant -∗
    {{{ ▷ TC 1 }}} tick v @ s ; E {{{ RET v ; True }}}.
  Proof.
    intros ?. iIntros "#Inv" (Ψ) "!# Hγ◯ HΨ".
    iLöb as "IH".
    wp_lam.
    (* open the invariant, in order to read the value n of location ℓ: *)
    wp_bind (! _)%E ;
    iInv timeCreditN as (n) ">(Hℓ & Hγ●)" "InvClose".
    wp_load.
    (* deduce that n ≥ 1, because we hold a time credit: *)
    iDestruct (own_auth_nat_le with "Hγ● Hγ◯") as %I.
    (* close the invariant: *)
    iMod ("InvClose" with "[ Hℓ Hγ● ]") as "_" ; [ by auto with iFrame | iModIntro ].
    wp_let.
    (* test whether n ≤ 0: *)
    wp_op ; destruct (bool_decide (n ≤ 0)) eqn:Im ; wp_if.
    (* — if n ≤ 0 then this is absurd, because we hold a time credit: *)
    - apply Is_true_eq_left, bool_decide_spec in Im.
      exfalso ; lia.
    (* — otherwise: *)
    - clear Im.
      wp_op.
      (* open the invariant again, in order to perform CAS on location ℓ: *)
      wp_bind (CAS _ _ _)%E ;
      iInv timeCreditN as (n') ">(Hℓ & Hγ●)" "InvClose".
      (* test whether the value ℓ is still k, by comparing n with n': *)
      destruct (nat_eq_dec n n') as [ <- | Hneq ].
      (* — if it holds, then CAS succeeds and ℓ is decremented: *)
      + wp_cas_suc.
        (* reform the invariant with n−1 instead of n: *)
        replace (Z.of_nat n - 1) with (Z.of_nat (n - 1)%nat) by lia.
        iMod (auth_nat_update_decr _ _ _ 1 with "Hγ● Hγ◯") as "[Hγ● Hγ◯]" ; first done.
        (* close the invariant: *)
        iMod ("InvClose" with "[ Hℓ Hγ● ]") as "_" ; [ by auto with iFrame | iModIntro ].
        (* finish: *)
        wp_if. by iApply "HΨ".
      (* — otherwise, CAS fails and ℓ is unchanged: *)
      + wp_cas_fail ; first (injection ; lia).
        (* close the invariant as is: *)
        iMod ("InvClose" with "[ Hℓ Hγ● ]") as "_" ; [ by auto with iFrame | iModIntro ] ; clear dependent n.
        wp_if.
        (* conclude using the induction hypothesis: *)
        iApply ("IH" with "Hγ◯ HΨ").
  Qed.

  Theorem tick_spec_simple v :
    TC_invariant -∗
    {{{ TC 1 }}} tick v {{{ RET v ; True }}}.
  Proof.
    iIntros "#Hinv" (Ψ) "!# HTC HΨ".
    by iApply (tick_spec with "Hinv [HTC//] HΨ").
  Qed.

  Lemma TC_implementation : TC_invariant -∗ TC_interface TC.
  Proof.
    iIntros "#Hinv". iSplit ; last iSplit ; last iSplit.
    - iPureIntro. by apply TC_timeless.
    - by iApply zero_TC.
    - iPureIntro. by apply TC_plus.
    - iIntros (v). by iApply (tick_spec_simple with "Hinv").
  Qed.

End TickSpec.



(*
 * Operational semantics of `tick`
 *)

Section Tick_lemmas.

  Context {Hloc : TickCounter}.

  (* Semantics in the “successful” case. *)

  Lemma exec_tick_success n v σ :
    prim_exec  (tick v) (<[ℓ := #(S n)]> σ)  v (<[ℓ := #n]> σ)  [].
  Proof. by apply exec_tick_success. Qed.

  (* Semantics in the “failing” case. *)

  Lemma not_safe_tick v σ :
    ¬ safe (tick v) (<[ℓ := #0]> σ).
  Proof.
    assert (prim_exec  (tick v) (<[ℓ := #0]> σ)  (#() #()) (<[ℓ := #0]> σ)  []) as Hexec.
    {
      unlock tick credits_tick generic_tick fail.
      eapply prim_exec_cons_nofork.
      { by prim_step. }
      simpl. eapply prim_exec_cons_nofork.
      { prim_step. apply lookup_insert. }
      simpl. eapply prim_exec_cons_nofork.
      { prim_step. }
      simpl. eapply prim_exec_cons_nofork.
      { by prim_step. }
      simpl. eapply prim_exec_cons_nofork.
      { by prim_step. }
      simpl. eapply prim_exec_cons_nofork.
      { by prim_step. }
      simpl. eapply prim_exec_cons_nofork.
      { by prim_step. }
      simpl. apply prim_exec_nil.
    }
    assert (¬ safe (#() #()) (<[ℓ := #0]> σ)) as Hnotsafe.
    {
      apply stuck_not_safe, head_stuck_stuck, ectxi_language_sub_redexes_are_values.
      - split ; first done. inversion 1.
      - intros [] ; try discriminate 1 ; inversion 1 ; by eauto.
    }
    intros Hsafe. eapply Hnotsafe, safe_exec_nofork, prim_exec_exec ; eassumption.
  Qed.

End Tick_lemmas.



(*
 * Simulation
 *)

Section Simulation.

  Context {Hloc : TickCounter}.

  (* Simulation in the “successful” case. *)

  Definition simulation_exec_success := simulation_exec_success fail.
  Definition simulation_exec_success' := simulation_exec_success' fail.

  (* Simulation in the “failing” case. *)

  Local Ltac not_safe_tick :=
    lazymatch goal with
    | |- ¬ safe ?e _ =>
        reshape_expr false e ltac:(fun K e' =>
          apply not_safe_fill' with K e' ; first reflexivity ;
          eapply not_safe_tick
        )
    end ;
    done.

  Lemma simulation_head_step_failure e1 σ1 κ e2 σ2 efs :
    head_step e1 σ1 κ e2 σ2 efs →
    ¬ safe «e1» S«σ1, 0».
  Proof.
    destruct 1 as
      [(* RecS *) f x e σ
      | | | | | | | | | | | |
      | (* ForkS *) e1 σ
      | | | | | | ] ;
    simpl_trans ;
    try not_safe_tick.
    (* RecS f x e σ : *)
    - eapply not_safe_prim_step; last prim_step.
      eapply not_safe_tick.
    (* ForkS e σ : *)
    - eapply not_safe_prim_step ; last prim_step.
      eapply not_safe_tick.
  Qed.

  Lemma simulation_prim_step_failure e1 σ1 κ e2 σ2 efs :
    prim_step e1 σ1 κ e2 σ2 efs →
    ¬ safe «e1» S«σ1, 0».
  Proof.
    intros [ K e1' e2' -> -> H ].
    rewrite translation_fill.
    by eapply not_safe_fill, simulation_head_step_failure.
  Qed.

  Lemma simulation_step_failure t1 σ1 κ t2 σ2 :
    step (t1, σ1) κ (t2, σ2) →
    ∃ e1, e1 ∈ t1 ∧
    ¬ safe «e1» S«σ1, 0».
  Proof.
    intros [e1 σ1_ e2 σ2_ efs t t' E1 E2 Hstep] ;
    injection E1 as -> <- ; injection E2 as -> <-.
    exists e1 ; split ; first set_solver.
    by eapply simulation_prim_step_failure.
  Qed.

  Local Lemma simulation_exec_failure_now n t1 σ1 t2 σ2 :
    relations.nsteps erased_step (S n) (t1, σ1) (t2, σ2) →
    ∃ e1, e1 ∈ t1 ∧
    ¬ safe «e1» S«σ1, 0».
  Proof.
    make_eq (S n) as Sn En.
    make_eq (t1, σ1) as config1 E1.
    destruct 1 as [ ? | ? ? [] ? [? ?] _ ], E1.
    - discriminate En.
    - by eapply simulation_step_failure.
  Qed.

  Lemma simulation_exec_failure m n e1 σ1 t2 σ2 :
    σ2 !! ℓ = None →
    relations.nsteps erased_step (m + S n) ([e1], σ1) (t2, σ2) →
    ¬ safe «e1» S«σ1, m».
  Proof.
    intros Hℓ Hnsteps.
    assert (
      ∃ t3 σ3,
        rtc erased_step (T«[e1]», S«σ1, m») (T«t3», S«σ3, 0») ∧
        ∃ e3, e3 ∈ t3 ∧
        ¬ safe «e3» S«σ3, 0»
    ) as (t3 & σ3 & Hsteps & e3 & E3 & Hsafe).
    {
      apply nsteps_split in Hnsteps as ((t3, σ3) & Hnsteps1to3 & Hnsteps3to2).
      exists t3, σ3 ; repeat split.
      - assert (σ3 !! ℓ = None) by (eapply loc_fresh_in_dom_nsteps ; cycle 1 ; eassumption).
        replace m with (m+0)%nat by lia.
        apply simulation_exec_success ; assumption.
      - by eapply simulation_exec_failure_now.
    }
    apply (elem_of_list_fmap_1 translation) in E3.
    eapply not_safe_exec ; eassumption.
  Qed.

End Simulation.



Section Soundness.

  (* See also `TimeCreditsAltProofs.v` *)

  (* assuming the safety of the translated expression,
   * a proof that the computation time of the original expression is bounded. *)

  Local Lemma gt_sum m n :
    (m > n)%nat → ∃ (k : nat), m = (n + S k)%nat.
  Proof.
    intro. exists (m - S n)%nat. lia.
  Qed.
  Lemma safe_tctranslation__bounded {Hloc : TickCounter} m e σ t2 σ2 n :
    σ2 !! ℓ = None →
    safe «e» S«σ, m» →
    relations.nsteps erased_step n ([e], σ) (t2, σ2) →
    (n ≤ m)%nat.
  Proof.
    intros Hfresh Hsafe Hnsteps.
    (* reasoning by contradiction: assume (n > m), ie. (n = m + S k) for some k: *)
    apply not_gt ; intros [k ->] % gt_sum.
    (* apply the simulation lemma: *)
    by eapply simulation_exec_failure.
  Qed.

  Lemma adequate_tctranslation__bounded m φ e σ :
    (∀ `{TickCounter}, adequate NotStuck «e» S«σ, m» (λ v σ, φ (invtranslationV v))) →
    bounded_time e σ m.
  Proof.
    intros Hadq.
    intros t2 σ2 k.
    (* build a location ℓ which is not in the domain of σ2: *)
    pose (Build_TickCounter (fresh (dom (gset loc) σ2))) as Hloc.
    assert (σ2 !! ℓ = None)
      by (unfold ℓ ; eapply (not_elem_of_dom (D:=gset loc)), is_fresh).
    specialize (Hadq Hloc) as Hsafe % safe_adequate.
    by eapply safe_tctranslation__bounded.
  Qed.

  Definition adequate_tctranslation__nadequate := adequate_translation__nadequate fail.

  (* now let’s combine the three results. *)

  Lemma adequate_tctranslation__adequate_and_bounded m φ e σ :
    (∀ (k : nat), (k ≥ m)%nat →
      ∀ `{TickCounter}, adequate NotStuck «e» S«σ, k» (λ v σ, φ (invtranslationV v))
    ) →
    adequate NotStuck e σ (λ v σ, φ v)  ∧  bounded_time e σ m.
  Proof.
    intros Hadq.
    assert (bounded_time e σ m) as Hbounded
      by (eapply adequate_tctranslation__bounded, Hadq ; lia).
    assert (nadequate NotStuck (m + 1) e σ φ) as Hadqm
      by (apply adequate_tctranslation__nadequate, Hadq ; lia).
    clear Hadq.
    split ; last done.
    split.
    - intros t2 σ2 v2 [n Hnsteps] % rtc_nsteps.
      assert (n ≤ m)%nat as Inm by by eapply Hbounded.
      eapply nadequate_result ; try done ; lia.
    - intros t2 σ2 e2 _ [n Hnsteps] % rtc_nsteps He2.
      assert (n ≤ m)%nat as Inm by by eapply Hbounded.
      eapply nadequate_not_stuck ; try done ; lia.
  Qed.

  (* finally, derive the adequacy assumption from a Hoare triple in Iris. *)

  Lemma spec_tctranslation__adequate_translation {Σ} m ψ e :
    (∀ `{timeCreditHeapG Σ},
      TC_invariant -∗
      {{{ TC m }}} «e» {{{ v, RET v ; ⌜ψ v⌝ }}}
    ) →
    ∀ `{timeCreditHeapPreG Σ} `{TickCounter} σ,
      ∀ (k : nat), (k ≥ m)%nat → adequate NotStuck «e» S«σ,k» (λ v σ, ψ v).
  Proof.
    intros Hspec HpreG Hloc σ k Ik.
    (* apply the adequacy results. *)
    apply (wp_adequacy _ _) ; simpl ; intros HinvG.
    (* … now we have to prove a WP. *)
    set σ' := S«σ».
    (* allocate the heap, including cell ℓ (on which we need to keep an eye): *)
    iMod (gen_heap_init (<[ℓ := #k]> σ')) as (Hheap) "(Hh● & Hℓ◯ & _)".
    iDestruct (big_sepM_lookup _ _ ℓ with "Hℓ◯") as "Hℓ◯".
    { by rewrite lookup_insert. }
    (* allocate the ghost state associated with ℓ: *)
    iMod (auth_nat_alloc k) as (γ) "[Hγ● Hγ◯]".
    (* packing all those bits, build the heap instance necessary to use time credits: *)
    pose (Build_timeCreditHeapG Σ (HeapGS Σ _ Hheap) _ _ γ)
      as HtcHeapG.
    (* create the invariant: *)
    iAssert (|={⊤}=> TC_invariant)%I with "[Hℓ◯ Hγ●]" as "> Hinv".
    {
      iApply inv_alloc.
      iExists k. iFrame.
    }
    iIntros (?) "!>".
    (* finally, use the user-given specification: *)
    iExists (λ σ _, gen_heap_interp σ), (λ _, True%I). iFrame.
    iDestruct (own_auth_nat_weaken _ _ _ Ik with "Hγ◯") as "Hγ◯".
    iApply (Hspec with "Hinv Hγ◯") ; auto.
  Qed.

  Theorem spec_tctranslation__adequate_and_bounded {Σ} m φ e :
    (∀ `{timeCreditHeapG Σ},
      TC_invariant -∗
      {{{ TC m }}} «e» {{{ v, RET v ; ⌜φ (invtranslationV v)⌝ }}}
    ) →
    ∀ {_ : timeCreditHeapPreG Σ} σ,
      adequate NotStuck e σ (λ v σ, φ v)  ∧  bounded_time e σ m.
  Proof.
    intros Hspec HpreG σ.
    apply adequate_tctranslation__adequate_and_bounded.
    intros k Ik Hloc. by eapply spec_tctranslation__adequate_translation.
  Qed.

  (* The abstract version of the theorem: *)
  Theorem abstract_spec_tctranslation__adequate_and_bounded {Σ} m φ e :
    (∀ `{heapGS Σ, Tick} (TC : nat → iProp Σ),
      TC_interface TC -∗
      {{{ TC m }}} «e» {{{ v, RET v ; ⌜φ (invtranslationV v)⌝ }}}
    ) →
    ∀ {_ : timeCreditHeapPreG Σ} σ,
      adequate NotStuck e σ (λ v σ, φ v)  ∧  bounded_time e σ m.
  Proof.
    intros Hspec HpreG σ.
    eapply spec_tctranslation__adequate_and_bounded ; try done.
    clear HpreG. iIntros (HtcHeapG) "#Hinv".
    iApply Hspec. by iApply TC_implementation.
  Qed.

  (* A simplification for common use-cases: when the return value does not
   * contain a closure, there is no need to compose the postcondition φ with
   * the translation: *)
  Theorem spec_tctranslation__adequate_and_bounded' {Σ} m (φ : val → Prop) e :
    (∀ v, φ v → closure_free v) →
    (∀ `{timeCreditHeapG Σ},
      TC_invariant -∗
      {{{ TC m }}} «e» {{{ v, RET v ; ⌜φ v⌝ }}}
    ) →
    ∀ {_ : timeCreditHeapPreG Σ} σ,
      adequate NotStuck e σ (λ v σ, φ v)  ∧  bounded_time e σ m.
  Proof.
    intros Hφ Hspec HpreG σ.
    apply (spec_tctranslation__adequate_and_bounded (Σ:=Σ)) ; try assumption.
    intros HtcHeapG.
    iIntros "#Htickinv !#" (Φ) "Htc Post".
    wp_apply (Hspec with "Htickinv Htc"). iIntros (v Hv).
    iApply ("Post" with "[%]").
    by apply closure_free_predicate.
  Qed.

End Soundness.



(*
 * Proof-mode tactics for proving WP of translated expressions
 *)

Section Tactics.

  Context {Σ : gFunctors}.

  Implicit Types Φ : val → iProp Σ.
  Implicit Types Δ : envs (uPredI (iResUR Σ)).

  (* concrete version: *)
  Lemma tac_wp_tick `{timeCreditHeapG Σ} Δ Δ' Δ'' s E i j n K (v : val) Φ :
    ↑timeCreditN ⊆ E →
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup i Δ  = Some (true, TC_invariant) →
    envs_lookup j Δ' = Some (false, TC (S n)) →
    envs_simple_replace j false (Esnoc Enil j (TC n)) Δ' = Some Δ'' →
    envs_entails Δ'' (WP fill K v @ s; E {{ Φ }}) →
    envs_entails Δ (WP fill K (App tick v) @ s; E {{ Φ }}).
  Proof.
    rewrite envs_entails_eq => HsubsetE ???? Hentails''.
    rewrite envs_lookup_intuitionistic_sound // intuitionistically_elim. apply wand_elim_r'.
    rewrite -wp_bind.
    eapply wand_apply ; first by (iIntros "HTC1 HΦ #Htick" ; iApply (tick_spec with "Htick HTC1 HΦ")).
    rewrite into_laterN_env_sound -later_sep /=. apply later_mono.
    rewrite envs_simple_replace_sound // ; simpl.
    rewrite TC_succ -sep_assoc. apply sep_mono_r.
    iIntros "[HTC Hwand] _". iApply Hentails''. iApply "Hwand" ; by iFrame.
  Qed.

(*
  (* TODO: abstract version: *)
  Lemma tac_wp_tick_abstr `{heapGS Σ} (TC : nat → iProp Σ) (tick : val) Δ Δ' Δ'' s E i j n K e (v : val) Φ :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup i Δ' = Some (true,  ∀ (v : val), {{{ TC 1%nat }}} tick v @ s ; E {{{ RET v ; True }}})%I →
    envs_lookup j Δ' = Some (false, TC (S n)) →
    envs_simple_replace i false (Esnoc Enil j (TC n)) Δ' = Some Δ'' →
    envs_entails Δ'' (WP fill K v @ s; E {{ Φ }}) →
    envs_entails Δ (WP fill K (App tick v) @ s; E {{ Φ }}).
  Admitted.
*)

End Tactics.

Ltac wp_tick ::=
  let solve_TICKCTXT _ :=
    iAssumptionCore || fail "wp_tick: cannot find TC_invariant" in
  let solve_TC _ :=
    iAssumptionCore || fail "wp_tick: cannot find TC (S _)" in
  iStartProof ;
  simpl_trans ;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
      first
        [ reshape_expr false e ltac:(fun K e' =>
            eapply (tac_wp_tick _ _ _ _ _ _ _ _ K)
          )
        | fail 1 "wp_tick: cannot find 'tick ?v' in" e ] ;
      [ try solve_ndisj
      | exact _
      | solve_TICKCTXT ()
      | solve_TC ()
      | proofmode.reduction.pm_reflexivity
      | wp_expr_simpl ]
  | _ => fail "wp_tick: not a 'wp'"
  end.
