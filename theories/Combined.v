From iris_time Require Import Base.
From iris.base_logic Require Import invariants.
From iris.algebra Require Import lib.gmap_view.
From iris.proofmode Require Import coq_tactics.
From iris_time.heap_lang Require Import proofmode notation adequacy lang.
From iris_time Require Import Auth_nat Auth_max_nat Reduction Tactics.
From iris_time Require Export Simulation.

Implicit Type e : expr.
Implicit Type v : val.
Implicit Type σ : state.
Implicit Type t : list expr.
Implicit Type K : ectx heap_ectx_lang.
Implicit Type m n max_tc max_tr : nat.
Implicit Type φ ψ : val → Prop.
Implicit Type Σ : gFunctors.



(*
 * Combined abstract interface for time credits and receipts
 *)

(* Ideally, this would be represented as a record (or a typeclass), but it has
 * to be an Iris proposition (iProp Σ) and not a Coq proposition (Prop). *)
Definition TCTR_interface `{irisGS heap_lang Σ, Tick}
  (TC : nat → iProp Σ)
  (max_tr : nat)
  (TR : nat → iProp Σ)
  (TRdup : nat → iProp Σ)
: iProp Σ := (
    ⌜∀ n, Timeless (TC n)⌝
  ∗ (|==> TC 0%nat)
  ∗ ⌜∀ m n, TC (m + n)%nat ≡ (TC m ∗ TC n)⌝
  ∗ ⌜∀ n, Timeless (TR n)⌝
  ∗ ⌜∀ n, Timeless (TRdup n)⌝
  ∗ ⌜∀ n, Persistent (TRdup n)⌝
  ∗ (∀ n, TR n ={⊤}=∗ TR n ∗ TRdup n)
  ∗ (|==> TR 0%nat)
(*   ∗ (|==> TRdup 0%nat) *)
  ∗ ⌜∀ m n, TR (m + n)%nat ≡ (TR m ∗ TR n)⌝
  ∗ ⌜∀ m n, TRdup (m `max` n)%nat ≡ (TRdup m ∗ TRdup n)⌝
(*   ∗ (TR max_tr ={⊤}=∗ False) *)
  ∗ (TRdup max_tr ={⊤}=∗ False)
  ∗ (∀ v n, {{{ TC 1%nat ∗ TRdup n }}} tick v {{{ RET v ; TR 1%nat ∗ TRdup (n+1)%nat }}})
)%I.



(*
 * Prerequisites on the global monoid Σ
 *)

Class tctrHeapPreG Σ := {
  tctrHeapPreG_heapPreG :> heapGpreS Σ ;
  tctrHeapPreG_inG_TC    :> inG Σ (authR natUR) ;
  tctrHeapPreG_inG_TR    :> inG Σ (authR natUR) ;
  tctrHeapPreG_inG_TRdup :> inG Σ (authR max_natUR) ;
}.

Class UseTC := useTC : bool.

Class tctrHeapG Σ := {
  tctrHeapG_heapG :> heapGS Σ ;
  tctrHeapG_inG_TC    :> inG Σ (authR natUR) ;
  tctrHeapG_inG_TR    :> inG Σ (authR natUR) ;
  tctrHeapG_inG_TRdup :> inG Σ (authR max_natUR) ;
  tctrHeapG_loc :> TickCounter ;
  tctrHeapG_name_TC    : gname ;
  tctrHeapG_name_TR    : gname ;
  tctrHeapG_name_TRdup : gname ;
  tctrHeapG_useTC      :> UseTC ;
}.

Local Notation γ := tctrHeapG_name_TC.
Local Notation γ1 := tctrHeapG_name_TR.
Local Notation γ2 := tctrHeapG_name_TRdup.
Local Notation ℓ := tick_counter.



(*
 * Implementation and specification of `tick`, `TC`, `TR` and `TRdup`
 *)



Definition fail : val :=
  λ: <>, #() #().

Definition loop : val :=
  rec: "f" <> := "f" #().

Global Instance tctr_tick {_:TickCounter} {_:UseTC} : Tick :=
  generic_tick (if useTC then fail else loop).



Section Definitions.

  Context `{tctrHeapG Σ}.

  Definition TC (n : nat) : iProp Σ :=
    if useTC then own γ (◯nat n) else True%I.

  (* Note: we can avoid the update modality by redefining TC like so:
         Definition TC' n : iProp Σ := ⌜n = 0%nat⌝ ∨ TC n. *)
  Lemma zero_TC :
    ⊢ |==> TC 0.
  Proof using.
    rewrite /TC ; destruct useTC.
    - by apply own_unit.
    - by iStartProof.
  Qed.
  Lemma TC_plus m n :
    TC (m + n) ≡ (TC m ∗ TC n)%I.
  Proof using.
    rewrite /TC ; destruct useTC.
    - by rewrite auth_frag_op own_op.
    - by iStartProof.
  Qed.
  Lemma TC_succ n :
    TC (S n) ≡ (TC 1%nat ∗ TC n)%I.
  Proof using. by rewrite (eq_refl : S n = 1 + n)%nat TC_plus. Qed.
  Lemma TC_weaken (n₁ n₂ : nat) :
    (n₂ ≤ n₁)%nat →
    TC n₁ -∗ TC n₂.
  Proof using.
    rewrite /TC ; destruct useTC.
    - by apply own_auth_nat_weaken.
    - done.
  Qed.

  Lemma TC_timeless n :
    Timeless (TC n).
  Proof using. rewrite /TC ; destruct useTC ; exact _. Qed.

  (* We give higher priorities to the (+) instances so that the (S n)
     instances are not chosen when m is a constant. *)
  Global Instance into_sep_TC_plus m n : IntoSep (TC (m + n)) (TC m) (TC n) | 0.
  Proof using. by rewrite /IntoSep TC_plus. Qed.
  Global Instance from_sep_TC_plus m n : FromSep (TC (m + n)) (TC m) (TC n) | 0.
  Proof using. by rewrite /FromSep TC_plus. Qed.
  Global Instance into_sep_TC_succ n : IntoSep (TC (S n)) (TC 1) (TC n) | 100.
  Proof using. by rewrite /IntoSep TC_succ. Qed.
  Global Instance from_sep_TC_succ n : FromSep (TC (S n)) (TC 1) (TC n) | 100.
  Proof using. by rewrite /FromSep [TC (S n)] TC_succ. Qed.

  Definition TR (n : nat) : iProp Σ :=
    own γ1 (◯nat n).

  Definition TRdup (n : nat) : iProp Σ :=
    own γ2 (◯ MaxNat n).

  (* Note: we can avoid the update modality by redefining TR like so:
         Definition TR' n : iProp Σ := ⌜n = 0%nat⌝ ∨ TR n. *)
  Lemma zero_TR :
    ⊢ |==> TR 0.
  Proof using. apply own_unit. Qed.
  Lemma TR_plus m n :
    TR (m + n) ≡ (TR m ∗ TR n)%I.
  Proof using. by rewrite /TR auth_frag_op own_op. Qed.
  Lemma TR_succ n :
    TR (S n) ≡ (TR 1 ∗ TR n)%I.
  Proof using. by rewrite (eq_refl : S n = 1 + n)%nat TR_plus. Qed.
  Lemma TR_weaken (n₁ n₂ : nat) :
    (n₂ ≤ n₁)%nat →
    TR n₁ -∗ TR n₂.
  Proof using. apply own_auth_nat_weaken. Qed.

  Lemma TR_timeless n :
    Timeless (TR n).
  Proof using. exact _. Qed.

  (* We give higher priorities to the (+) instances so that the (S n)
     instances are not chosen when m is a constant. *)
  Global Instance into_sep_TR_plus m n : IntoSep (TR (m + n)) (TR m) (TR n) | 0.
  Proof using. by rewrite /IntoSep TR_plus. Qed.
  Global Instance from_sep_TR_plus m n : FromSep (TR (m + n)) (TR m) (TR n) | 0.
  Proof using. by rewrite /FromSep TR_plus. Qed.
  Global Instance into_sep_TR_succ n : IntoSep (TR (S n)) (TR 1) (TR n) | 100.
  Proof using. by rewrite /IntoSep TR_succ. Qed.
  Global Instance from_sep_TR_succ n : FromSep (TR (S n)) (TR 1) (TR n) | 100.
  Proof using. by rewrite /FromSep [TR (S n)] TR_succ. Qed.

  (* Note: we can avoid the update modality by redefining TRdup like so:
         Definition TRdup' n : iProp Σ := ⌜n = 0%nat⌝ ∨ TRdup n. *)
  Lemma zero_TRdup :
    ⊢ |==> TRdup 0.
  Proof using. apply own_unit. Qed.
  Lemma TRdup_max m n :
    TRdup (m `max` n) ≡ (TRdup m ∗ TRdup n)%I.
  Proof using. by rewrite /TRdup -own_op -auth_frag_op. Qed.
  Lemma TRdup_weaken (n₁ n₂ : nat) :
    (n₂ ≤ n₁)%nat →
    TRdup n₁ -∗ TRdup n₂.
  Proof using. apply own_auth_max_nat_weaken. Qed.

  Lemma TRdup_timeless n :
    Timeless (TRdup n).
  Proof using. exact _. Qed.
  Lemma TRdup_persistent n :
    Persistent (TRdup n).
  Proof using. exact _. Qed.

  Global Instance into_sep_TRdup_max m n : IntoSep (TRdup (m `max` n)) (TRdup m) (TRdup n).
  Proof using. by rewrite /IntoSep TRdup_max. Qed.
  Global Instance from_sep_TRdup_max m n : FromSep (TRdup (m `max` n)) (TRdup m) (TRdup n).
  Proof using. by rewrite /FromSep TRdup_max. Qed.

  Definition tctrN := nroot .@ "combinedTimeCreditTimeReceipt".

  Context (max_tr : nat).

  Definition TCTR_invariant : iProp Σ :=
    inv tctrN (
      ∃ (m:nat),
        ⌜(m < max_tr)%nat⌝
      ∗ ℓ ↦ #m
      ∗ (if useTC then own γ (●nat m) else True)
      ∗ own γ1 (●nat (max_tr - 1 - m))
      ∗ own γ2 (● MaxNat (max_tr - 1 - m))
    )%I.

  Lemma TR_nmax_absurd (E : coPset) :
    ↑tctrN ⊆ E →
    TCTR_invariant -∗ TR max_tr ={E}=∗ False.
  Proof using.
    iIntros (?) "#Inv Hγ1◯".
    iInv tctrN as (m) "(>I & _ & _ & >Hγ1● & _)" "InvClose" ; iDestruct "I" as %I.
    iDestruct (own_auth_nat_le with "Hγ1● Hγ1◯") as %I'.
    exfalso ; lia.
  Qed.
  Lemma TR_lt_nmax n (E : coPset) :
    ↑tctrN ⊆ E →
    TCTR_invariant -∗ TR n ={E}=∗ TR n ∗ ⌜n < max_tr⌝%nat.
  Proof using.
    iIntros (?) "#Inv Hγ1◯".
    destruct (le_lt_dec max_tr n) as [ I | I ] ; last by iFrame.
    iDestruct (TR_weaken n max_tr with "Hγ1◯") as "Hγ1◯" ; first done.
    iDestruct (TR_nmax_absurd with "Inv Hγ1◯") as ">?" ; first done.
    done.
  Qed.

  Lemma TRdup_nmax_absurd (E : coPset) :
    ↑tctrN ⊆ E →
    TCTR_invariant -∗ TRdup max_tr ={E}=∗ False.
  Proof using.
    iIntros (?) "#Inv Hγ2◯".
    iInv tctrN as (m) "(>I & _ & _ & _ & >Hγ2●)" "InvClose" ; iDestruct "I" as %I.
    iDestruct (own_auth_max_nat_le with "Hγ2● Hγ2◯") as %I'. exfalso ; lia.
  Qed.
  Lemma TRdup_lt_nmax n (E : coPset) :
    ↑tctrN ⊆ E →
    TCTR_invariant -∗ TRdup n ={E}=∗ TRdup n ∗ ⌜n < max_tr⌝%nat.
  Proof using.
    iIntros (?) "#Inv Hγ1◯".
    destruct (le_lt_dec max_tr n) as [ I | I ] ; last by iFrame.
    iDestruct (TRdup_weaken n max_tr with "Hγ1◯") as "Hγ1◯" ; first done.
    iDestruct (TRdup_nmax_absurd with "Inv Hγ1◯") as ">?" ; first done.
    done.
  Qed.

  Lemma TR_TRdup (E : coPset) n :
    ↑tctrN ⊆ E →
    TCTR_invariant -∗ TR n ={E}=∗ TR n ∗ TRdup n.
  Proof using.
    iIntros (?) "#Inv Hγ1◯".
    iInv tctrN as (m) "(>I & >Hℓ & Hγ● & >Hγ1● & >Hγ2●)" "InvClose".
    iDestruct (own_auth_nat_le with "Hγ1● Hγ1◯") as %I'.
    iDestruct (auth_max_nat_update_read_auth with "Hγ2●") as ">[Hγ2● Hγ2◯]".
    iAssert (TR n ∗ TRdup n)%I with "[$Hγ1◯ Hγ2◯]" as "$". {
      rewrite (_ : (max_tr-1-m) = (max_tr-1-m) `max` n)%nat ; last lia.
      iDestruct "Hγ2◯" as "[_ $]".
    }
    iApply "InvClose". auto with iFrame.
  Qed.

  Theorem loop_spec s E (Φ : val → iProp Σ) :
    ⊢ WP loop #() @ s ; E {{ Φ }}.
  Proof.
    iLöb as "IH". wp_rec. iExact "IH".
  Qed.

  Theorem tick_spec s E (v : val) n :
    ↑tctrN ⊆ E →
    TCTR_invariant -∗
    {{{ ▷ TC 1 ∗ ▷ TRdup n }}} tick v @ s ; E {{{ RET v ; TR 1 ∗ TRdup (n+1) }}}.
  Proof using.
    intros ?. iIntros "#Inv" (Ψ) "!# [Hγ◯ Hγ2◯] HΨ".
    iLöb as "IH".
    wp_lam.
    (* open the invariant, in order to read the value m of location ℓ: *)
    wp_bind (! _)%E ;
    iInv tctrN as (m) "(>I & >Hℓ & Hγ● & >Hγ1● & >Hγ2●)" "InvClose".
    wp_load.
    (* in the case where we are using time credits, deduce that m ≥ 1,
       because we hold a time credit: *)
    iAssert (⌜useTC = true⌝ -∗ ⌜1 ≤ m⌝)%I%nat with "[Hγ● Hγ◯]" as "#J".
    {
      rewrite /TC ; iIntros "->".
      by iApply (own_auth_nat_le with "Hγ● Hγ◯").
    }
    (* close the invariant: *)
    iMod ("InvClose" with "[ I Hℓ Hγ● Hγ1● Hγ2● ]") as "_" ; [ by auto with iFrame | iModIntro ].
    wp_let.
    (* test whether m ≤ 0: *)
    wp_op. case_bool_decide as J' ; wp_if.
    (* — if m ≤ 0: *)
    - destruct useTC.
      (* if we use TC, then m ≤ 0 is absurd, because we hold a time credit: *)
      + iDestruct ("J" with "[//]") as %J.
        exfalso ; lia.
      (* if we don’t, then we loop indefinitely, which gives us any spec we want
         (because we are reasoning in partial correctness): *)
      + iApply loop_spec.
    (* — otherwise: *)
    - wp_op.
      (* open the invariant again, in order to perform CAS on location ℓ: *)
      wp_bind (CAS _ _ _)%E ;
      iInv tctrN as (m') "(>I & >Hℓ & Hγ● & >Hγ1● & >Hγ2●)" "InvClose".
      (* test whether the value ℓ is still m, by comparing m with m': *)
      destruct (nat_eq_dec m m') as [ <- | Hneq ].
      (* — if it holds, then CAS succeeds and ℓ is decremented: *)
      + wp_cas_suc.
        (* reform the invariant with m−1 instead of m: *)
        replace (Z.of_nat m - 1) with (Z.of_nat (m - 1)%nat) by lia.
        iAssert (|==> if useTC then own γ (●nat (m-1)) else True)%I with "[Hγ● Hγ◯]" as ">Hγ●".
        {
          rewrite /TC ; destruct useTC ; last done.
          by iMod (auth_nat_update_decr _ _ _ 1 with "Hγ● Hγ◯") as "[$ _]".
        }
        iMod (auth_nat_update_incr _ _ 1 with "Hγ1●") as "[Hγ1● Hγ1◯]".
        iMod (auth_max_nat_update_incr' _ _ _ 1 with "Hγ2● Hγ2◯") as "[Hγ2● Hγ2◯]".
        iDestruct "I" as %I.
        replace (max_tr - 1 - m + 1)%nat with (max_tr - 1 - (m - 1))%nat by lia.
        assert ((m-1) < max_tr)%nat by lia.
        (* close the invariant: *)
        iMod ("InvClose" with "[ Hℓ Hγ● Hγ1● Hγ2● ]") as "_" ; [ by auto with iFrame | iModIntro ].
        (* finish: *)
        wp_if. iApply "HΨ" ; by iFrame.
      (* — otherwise, CAS fails and ℓ is unchanged: *)
      + wp_cas_fail ; first (injection ; lia).
        (* close the invariant as is: *)
        iMod ("InvClose" with "[ I Hℓ Hγ● Hγ1● Hγ2● ]") as "_" ; [ by auto with iFrame | iModIntro ].
        wp_if.
        (* conclude using the induction hypothesis: *)
        iApply ("IH" with "Hγ◯ Hγ2◯ HΨ").
  Qed.

  Theorem tick_spec_simple v n :
    TCTR_invariant -∗
    {{{ TC 1 ∗ TRdup n }}} tick v {{{ RET v ; TR 1 ∗ TRdup (n+1) }}}.
  Proof using.
    iIntros "#Hinv" (Ψ) "!# [ HTC HTR ] HΨ".
    by iApply (tick_spec with "Hinv [$HTC $HTR] HΨ").
  Qed.

  Lemma TC_implementation : TCTR_invariant -∗ TCTR_interface TC max_tr TR TRdup.
  Proof using.
    iIntros "#Hinv". repeat iSplitR.
    - iPureIntro. by apply TC_timeless.
    - by iApply zero_TC.
    - iPureIntro. by apply TC_plus.
    - iPureIntro. by apply TR_timeless.
    - iPureIntro. by apply TRdup_timeless.
    - iPureIntro. by apply TRdup_persistent.
    - iIntros (n). by iApply (TR_TRdup with "Hinv").
    - by iApply zero_TR.
    - iPureIntro. by apply TR_plus.
    - iPureIntro. by apply TRdup_max.
    - by iApply (TRdup_nmax_absurd with "Hinv").
    - iIntros (v n). by iApply (tick_spec_simple with "Hinv").
  Qed.

End Definitions.

(*
 * Proof-mode tactics for proving WP of translated expressions
 *)

Lemma tac_wp_tick `{tctrHeapG Σ} Δ pe Δ1 Δ2 Δ3 Δ' i i' n max_tc s E K (v : val) Φ :
  ↑tctrN ⊆ E →
  MaybeIntoLaterNEnvs 1 Δ Δ1 →

  envs_lookup i Δ = Some (pe, TCTR_invariant max_tc) →

  envs_lookup i' Δ1 = Some (false, TC (S n)) →
  envs_simple_replace i' false (Esnoc Enil i' (TC n)) Δ1 = Some Δ2 →

  (∃ j pe' p, envs_lookup j Δ2 = Some (pe', TRdup p) ∧
              envs_simple_replace j pe' (Esnoc Enil j (TRdup (S p))) Δ2 = Some Δ3) ∨
  Δ2 = Δ3 →

  (∃ j n, envs_lookup j Δ3 = Some (false, TR n) ∧
          envs_simple_replace j false (Esnoc Enil j (TR (S n))) Δ3 = Some Δ') ∨
  Δ3 = Δ' →

  envs_entails Δ' (WP fill K v @ s; E {{ Φ }}) →
  envs_entails Δ (WP fill K (App tick v) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=>??? HTC1 HTC2 HTRdup HTR HWP.
  iIntros "HΔ".
  iAssert (TCTR_invariant max_tc) as "#Hinv".
  { destruct pe.
    iDestruct (envs_lookup_sound _ i true with "HΔ") as "[? _]"=>//.
    iDestruct (envs_lookup_sound _ i false with "HΔ") as "[? _]"=>//. }
  iDestruct (into_laterN_env_sound with "HΔ") as "HΔ1"=>//.
  iDestruct (envs_simple_replace_singleton_sound with "HΔ1") as "[HTC HΔ2]"=>//=.
  iDestruct "HTC" as "[HTC HTC']". iDestruct ("HΔ2" with "HTC'") as "HΔ2".
  iApply wp_bind.
  destruct HTR as [(j & n' & HTR1 & HTR2)| ->],
           HTRdup as [(j' & pe'' & p & HTRDup1 & HTRDup2)| ->].
  - iDestruct (envs_simple_replace_singleton_sound with "HΔ2") as "[HTRdup HΔ3]"=>//.
    rewrite bi.intuitionistically_if_elim -bi.intuitionistically_intuitionistically_if.
    iDestruct "HTRdup" as "#>HTRdup".
    iApply (tick_spec with "[//] [$HTC $HTRdup]")=>//.
    iIntros "!> [HTR #HTRdup']". iApply HWP.
    rewrite Nat.add_comm. iSpecialize ("HΔ3" with "[//]").
    iDestruct (envs_simple_replace_singleton_sound with "HΔ3") as "[HTR' HΔ']"=>//=.
    iCombine "HTR HTR'" as "HTR". iDestruct ("HΔ'" with "HTR") as "$".
  - iMod zero_TRdup as "HTRdup".
    iApply (tick_spec with "[//] [$HTC $HTRdup]")=>//. iIntros "!> [HTR _]". iApply HWP.
    iDestruct (envs_simple_replace_singleton_sound with "HΔ2") as "[HTR' HΔ']"=>//=.
    iCombine "HTR HTR'" as "HTR". iDestruct ("HΔ'" with "HTR") as "$".
  - iDestruct (envs_simple_replace_singleton_sound with "HΔ2") as "[HTRdup HΔ']"=>//.
    rewrite bi.intuitionistically_if_elim -bi.intuitionistically_intuitionistically_if.
    iDestruct "HTRdup" as "#>HTRdup".
    iApply (tick_spec with "[//] [$HTC $HTRdup]")=>//. iIntros "!> [_ #HTRdup']".
    iApply HWP. rewrite Nat.add_comm. iDestruct ("HΔ'" with "[//]") as "$".
  - iMod zero_TRdup as "HTRdup".
    iApply (tick_spec with "[//] [$HTC $HTRdup]")=>//.
    iIntros "!> [_ #HTRdup']". by iApply HWP.
Qed.

Ltac wp_tick ::=
  iStartProof ;
  simpl_trans ;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
      first
        [ reshape_expr false e ltac:(fun K e' =>
            eapply (tac_wp_tick _ _ _ _ _ _ _ _ _ _ _ _ K)
          )
        | fail 1 "wp_tick: cannot find 'tick ?v' in" e ] ;
      [ try solve_ndisj
      | exact _
      | (* lookup invariant: *) (iAssumptionCore || fail "wp_tick: cannot find TR_invariant")
      | (* lookup TC *) (iAssumptionCore || fail "wp_tick: cannot find (TC (S _))")
      | (* replace TC *) proofmode.reduction.pm_reflexivity
      | (* lookup TRdup: *) (
        left; eexists _, _, _; split;
        [iAssumptionCore | proofmode.reduction.pm_reflexivity]
        || right; reflexivity)
      | (* lookup TR:    *) (
        left; eexists _, _; split;
        [iAssumptionCore | proofmode.reduction.pm_reflexivity]
        || right; reflexivity)
      | wp_expr_simpl ]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
      fail "wp_tick is not implemented for twp"
  | _ => fail "wp_tick: not a 'wp'"
  end.



(*
 * Simulation
 *)

Section Simulation.

  (* Simulation in the “successful” case. *)

  Context {Hloc : TickCounter}.
  Context {useTC : UseTC}.

  Lemma exec_tick_success n v σ :
    prim_exec  (tick v) (<[ℓ := #(S n)]> σ)  v (<[ℓ := #n]> σ)  [].
  Proof. by apply exec_tick_success. Qed.

  Definition simulation_exec_success := simulation_exec_success (if useTC then fail else loop).
  Definition simulation_exec_success' := simulation_exec_success' (if useTC then fail else loop).

  (* Simulation in the “failing” case. *)

  Context (HuseTC : useTC = true).

  Lemma not_safe_tick v σ :
    ¬ safe (tick v) (<[ℓ := #0]> σ).
  Proof.
    assert (prim_exec  (tick v) (<[ℓ := #0]> σ)  (#() #()) (<[ℓ := #0]> σ)  []) as Hexec.
    {
      unlock tick tctr_tick generic_tick fail ; rewrite HuseTC.
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
    - eapply not_safe_prim_step ; last prim_step.
      not_safe_tick.
    (* ForkS e σ : *)
    - eapply not_safe_prim_step ; last prim_step.
      not_safe_tick.
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



(*
 * Soundness
 *)

Section Soundness.

(** Part of the proof of soundness which is specific to the case where
 ** time credits are used (m < max_tr). **)

  (* assuming the safety of the translated expression,
   * a proof that the computation time of the original expression is bounded. *)

  Local Lemma gt_sum m n :
    (m > n)%nat → ∃ (k : nat), m = (n + S k)%nat.
  Proof.
    intro. exists (m - S n)%nat. lia.
  Qed.

  Lemma safe_tctranslation__bounded {Hloc : TickCounter} {useTC : UseTC} m e σ t2 σ2 n :
    useTC = true →
    σ2 !! ℓ = None →
    safe «e» S«σ, m» →
    relations.nsteps erased_step n ([e], σ) (t2, σ2) →
    (n ≤ m)%nat.
  Proof.
    intros HuseTC Hfresh Hsafe Hnsteps.
    (* reasoning by contradiction: assume (n > m), ie. (n = m + S k) for some k: *)
    apply not_gt ; intros [k ->] % gt_sum.
    (* apply the simulation lemma: *)
    by eapply simulation_exec_failure.
  Qed.

  (* assuming the safety of the translated expression,
   * a proof that the original expression is safe. *)

  Lemma safe_tctranslation__safe_here {Hloc : TickCounter} {useTC : UseTC} m e σ :
    useTC = true →
    loc_fresh_in_expr ℓ e →
    safe «e» S«σ, m» →
    is_Some (to_val e) ∨ reducible e σ.
  Proof.
    intros HuseTC Hfresh Hsafe.
    (* case analysis on whether e is a value… *)
    destruct (to_val e) as [ v | ] eqn:Hnotval.
    (* — if e is a value, then we get the result immediately: *)
    - left. eauto.
    (* — if e is not a value, then we show that it is reducible: *)
    - right.
      (* we decompose e into a maximal evaluation context K and a head-redex: *)
      pose proof (not_val_fill_active_item _ Hnotval) as He ; clear Hnotval.
      destruct He as [ (K & x & ->) |
                     [ (K & e1 & ->) |
                     [ (K & f & x & e1 & ->) |
                       (K & ki & v & -> & Hactive) ]]].
      (* — either e = Var x: *)
      + (* then Var x is stuck *)
        exfalso. eapply stuck_not_safe; [|done]. rewrite translation_fill.
        apply stuck_fill, head_stuck_stuck.
        { split; [done|]. intros ???? Hstep. inversion Hstep. }
        apply ectxi_language_sub_redexes_are_values=>-[] //.
      (* — either e = K[Fork e1]: *)
      + (* then we easily derive a reduction from e: *)
        eexists _, _, _, _. apply Ectx_step', ForkS.
      (* — either e = K[Rec f x e1]: *)
      + (* then we easily derive a reduction from e: *)
        eexists _, _, _, _. apply Ectx_step', RecS.
      (* — or e = K[ki[v]] where ki is an active item: *)
      + (* it is enough to show that ki[v] is reducible: *)
        apply loc_fresh_in_expr_fill_inv in Hfresh ;
        rewrite -> translation_fill in Hsafe ; apply safe_fill_inv in Hsafe ;
        apply reducible_fill ;
        clear K.
        (* we deduce the reducibility of ki[v] from that of «ki»[«v»]: *)
        eapply active_item_translation_reducible ; [ done | done | ].
        (* remind that « ki[v] » = «ki»[tick «v»]: *)
        rewrite -> translation_fill_item_active in Hsafe ; last done.
        (* we have that «ki»[tick «v»] reduces to «ki»[«v»]
         * (thanks to the safety hypothesis, m ≥ 1 and ‘tick’ can be run): *)
        assert (
          prim_exec (fill_item Ki«ki» (tick V«v»)) S«σ, m»
                    (fill_item Ki«ki» V«v»)        S«σ, m-1» []
        ) as Hsteps % prim_exec_exec.
        {
          assert (fill [Ki«ki»] = fill_item Ki«ki») as E by reflexivity ; destruct E.
          apply prim_exec_fill. apply safe_fill_inv in Hsafe.
          (* This is where the unsafe behavior of “tick” is used: *)
          destruct m as [ | m ] ; first (exfalso ; eapply not_safe_tick ; eassumption).
          replace (S m - 1)%nat with m by lia.
          apply exec_tick_success.
        }
        (* using the safety of «ki»[tick «v»], we proceed by case analysis… *)
        eapply Hsafe in Hsteps as [ Hisval | Hred ] ; auto using elem_of_list_here.
        (* — either «ki»[«v»] is a value: this is not possible because ki is active. *)
        * simpl in Hisval. rewrite active_item_not_val in Hisval ;
          [ by apply is_Some_None in Hisval | by apply is_active_translationKi ].
        (* — or «ki»[«v»] reduces to something: this is precisely what we need. *)
        * exact Hred.
  Qed.

  Lemma safe_tctranslation__safe {Hloc : TickCounter} {useTC : UseTC} m e σ t2 σ2 e2 :
    useTC = true →
    loc_fresh_in_expr ℓ e2 →
    σ2 !! ℓ = None →
    safe «e» S«σ, m» →
    rtc erased_step ([e], σ) (t2, σ2) →
    e2 ∈ t2 →
    is_Some (to_val e2) ∨ reducible e2 σ2.
  Proof.
    intros HuseTC Hℓe Hℓσ Hsafe [n Hnsteps] % rtc_nsteps He2.
    assert (n ≤ m)%nat by by eapply safe_tctranslation__bounded.
    assert (safe «e2» S«σ2, m-n») as Hsafe2.
    {
      eapply safe_exec.
      - eapply elem_of_list_fmap_1. eassumption.
      - eassumption.
      - change [«e»] with T«[e]». apply simulation_exec_success' ; auto.
    }
    by eapply safe_tctranslation__safe_here.
  Qed.

  (* assuming the adequacy of the translated expression,
   * a proof that the original expression has adequate results. *)

  Lemma adequate_tctranslation__adequate_result {Hloc : TickCounter} {useTC : UseTC} m φ e σ t2 σ2 v2 :
    useTC = true →
    σ2 !! ℓ = None →
    adequate NotStuck «e» S«σ, m» (λ v σ, φ (invtranslationV v)) →
    rtc erased_step ([e], σ) (Val v2 :: t2, σ2) →
    φ v2.
  Proof.
    intros HuseTC Hfresh Hadq [n Hnsteps] % rtc_nsteps.
    assert (safe «e» S«σ, m») as Hsafe by by eapply safe_adequate.
    assert (n ≤ m)%nat by by eapply safe_tctranslation__bounded.
    replace (φ v2) with ((φ ∘ invtranslationV) (translationV v2))
      by (simpl ; by rewrite invtranslationV_translationV).
    eapply (adequate_result _ _ _ (λ v σ, φ (invtranslationV v))) ; first done.
    change [«e»%E] with T«[e]».
    replace (Val «v2» :: _) with (T«Val v2 :: t2») by done.
    eapply simulation_exec_success' ; eauto.
  Qed.

  (* now let’s combine the three results. *)

  Lemma adequate_tctranslation__adequate_and_bounded m φ e σ :
    let useTC : UseTC := true in
    (∀ `{TickCounter}, adequate NotStuck «e» S«σ, m» (λ v σ, φ (invtranslationV v))) →
    adequate NotStuck e σ (λ v σ, φ v)  ∧  bounded_time e σ m.
  Proof.
    intros useTC Hadq.
    split ; first split.
    (* (1) adequate result: *)
    - intros t2 σ2 v2 Hsteps.
      (* build a location ℓ which is not in the domain of σ2: *)
      pose (Build_TickCounter (fresh (dom (gset loc) σ2))) as Hloc.
      assert (σ2 !! ℓ = None)
        by (simpl ; eapply (not_elem_of_dom (D:=gset loc)), is_fresh).
      by eapply adequate_tctranslation__adequate_result.
    (* (2) safety: *)
    - intros t2 σ2 e2 _ Hsteps He2.
      (* build a location ℓ which is fresh in e2 and in the domain of σ2: *)
      pose (set1 := loc_set_of_expr e2 : gset loc).
      pose (set2 := dom (gset loc) σ2 : gset loc).
      pose (Build_TickCounter (fresh (set1 ∪ set2))) as Hloc.
      eassert (ℓ ∉ set1 ∪ set2) as [Hℓ1 Hℓ2] % not_elem_of_union
        by (unfold ℓ ; apply is_fresh).
      assert (loc_fresh_in_expr ℓ e2)
        by by apply loc_not_in_set_is_fresh_in_expr.
      assert (σ2 !! ℓ = None)
        by by (simpl ; eapply (not_elem_of_dom (D:=gset loc))).
      specialize (Hadq Hloc) as Hsafe % safe_adequate.
      by eapply safe_tctranslation__safe.
    (* (3) bounded time: *)
    - intros t2 σ2 k.
      (* build a location ℓ which is not in the domain of σ2: *)
      pose (Build_TickCounter (fresh (dom (gset loc) σ2))) as Hloc.
      assert (σ2 !! ℓ = None)
        by (unfold ℓ ; eapply (not_elem_of_dom (D:=gset loc)), is_fresh).
      specialize (Hadq Hloc) as Hsafe % safe_adequate.
      by eapply safe_tctranslation__bounded.
  Qed.

(** Part of the proof of soundness which is specific to the case where
 ** time credits are not used (m ≥ max_tr). **)

  (* assuming the adequacy of the translated expression,
   * a proof that the original expression is n-adequate. *)

  Definition adequate_trtranslation__nadequate := adequate_translation__nadequate loop.

(** Part of the proof which is common to both cases. **)

  (* from a Hoare triple in Iris,
   * derive the adequacy of the translated expression. *)

  Lemma spec_tctranslation__adequate_translation {Σ} max_tr m ψ e :
    (0 < max_tr)%nat →
    (∀ `{tctrHeapG Σ},
      TCTR_invariant max_tr -∗
      {{{ TC m }}} «e» {{{ v, RET v ; ⌜ψ v⌝ }}}
    ) →
    ∀ `{tctrHeapPreG Σ} `{TickCounter} σ,
      let useTC : UseTC := bool_decide (m < max_tr)%nat in
      let M : nat := min m (max_tr-1) in
      adequate NotStuck «e» S«σ,M» (λ v σ, ψ v).
  Proof.
    intros Imax_tr Hspec HpreG Hloc σ useTC M.
    assert (M ≤ m)%nat by (unfold M ; lia).
    assert (M < max_tr)%nat by (unfold M ; lia).
    (* apply the adequacy results. *)
    apply (wp_adequacy _ _) ; simpl ; intros HinvG.
    (* … now we have to prove a WP. *)
    set σ' := S«σ».
    (* allocate the heap, including cell ℓ (on which we need to keep an eye): *)
    iMod (gen_heap_init (<[ℓ := #M]> σ')) as (Hheap) "(Hh● & Hℓ◯ & _)".
    iDestruct (big_sepM_lookup _ _ ℓ with "Hℓ◯") as "Hℓ◯".
    { by rewrite lookup_insert. }
    (* allocate the ghost state associated with ℓ: *)
    iAssert (|==> ∃ γ,
        (if useTC then own γ (● M) else True)
      ∗ (if useTC then own γ (◯ m) else True)
    )%I as "Hγalloc".
    {
      rewrite /useTC ; case_bool_decide ; last by iExists inhabitant.
      rewrite (_ : M = m) ; last by (rewrite /M ; lia).
      iMod (auth_nat_alloc m) as (γ) "[Hγ● Hγ◯]".
      auto with iFrame.
    }
    iMod "Hγalloc" as (γ) "[Hγ● Hγ◯]".
    iMod (auth_nat_alloc (max_tr-1-M)) as (γ1) "[Hγ1● _]".
    iMod (auth_max_nat_alloc (max_tr-1-M)) as (γ2) "[Hγ2● _]".
    (* packing all those bits, build the heap instance necessary to use time credits: *)
    pose (Build_tctrHeapG Σ (HeapGS Σ _ Hheap) _ _ _ _ γ γ1 γ2 _)
      as HtcHeapG.
    (* create the invariant: *)
    iAssert (|={⊤}=> TCTR_invariant max_tr)%I with "[Hℓ◯ Hγ● Hγ1● Hγ2●]" as "> Hinv".
    {
      iApply inv_alloc.
      iExists M. by iFrame.
    }
    iIntros (?) "!>".
    (* finally, use the user-given specification: *)
    iExists (λ σ _, gen_heap_interp σ), (λ _, True%I). iFrame.
    iApply (Hspec $ HtcHeapG with "Hinv Hγ◯") ; auto.
  Qed.

  (* the final soundness theorem. *) 

  Theorem tctr_sound {Σ} max_tr m φ e :
    (0 < max_tr)%nat →
    (∀ `{tctrHeapG Σ},
      TCTR_invariant max_tr -∗
      {{{ TC m }}} «e» {{{ v, RET v ; ⌜φ (invtranslationV v)⌝ }}}
    ) →
    ∀ {_ : tctrHeapPreG Σ} σ,
      if bool_decide (m < max_tr)%nat then
        adequate NotStuck e σ (λ v σ, φ v)  ∧  bounded_time e σ m
      else
        nadequate NotStuck (max_tr-1) e σ (λ v, φ v).
  Proof.
    intros Imax_tr Hspec HpreG σ.
    pose H := (spec_tctranslation__adequate_translation max_tr m _ e Imax_tr Hspec) ;
    clearbody H. clear Hspec.
    case_bool_decide.
    - rewrite (_ : min m (max_tr-1) = m)%nat in H ; last by lia.
      apply adequate_tctranslation__adequate_and_bounded.
      intros Hloc ; by apply H.
    - rewrite (_ : min m (max_tr-1) = (max_tr-1))%nat in H ; last by lia.
      apply adequate_trtranslation__nadequate.
      intros Hloc. by apply H.
  Qed.

  (* abstract version of the theorem. *)
  Theorem tctr_sound_abstract {Σ} max_tr m φ e :
    (0 < max_tr)%nat →
    (∀ `{heapGS Σ, Tick} (TC TR TRdup : nat → iProp Σ),
      TCTR_interface TC max_tr TR TRdup -∗
      {{{ TC m }}} «e» {{{ v, RET v ; ⌜φ (invtranslationV v)⌝ }}}
    ) →
    ∀ {_ : tctrHeapPreG Σ} σ,
      if bool_decide (m < max_tr)%nat then
        adequate NotStuck e σ (λ v σ, φ v)  ∧  bounded_time e σ m
      else
        nadequate NotStuck (max_tr-1) e σ (λ v, φ v).
  Proof.
    intros Imax_tr Hspec HpreG σ.
    eapply tctr_sound ; try done.
    clear HpreG. iIntros (HtcHeapG) "#Hinv".
    iApply Hspec. by iApply TC_implementation.
  Qed.

  (* A simplification for common use-cases: when the return value does not
   * contain a closure, there is no need to compose the postcondition φ with
   * the translation: *)
  Theorem tctr_sound_simple {Σ} max_tr m φ e :
    (∀ v, φ v → closure_free v) →
    (0 < max_tr)%nat →
    (∀ `{tctrHeapG Σ},
      TCTR_invariant max_tr -∗
      {{{ TC m }}} «e» {{{ v, RET v ; ⌜φ v⌝ }}}
    ) →
    ∀ {_ : tctrHeapPreG Σ} σ,
      if bool_decide (m < max_tr)%nat then
        adequate NotStuck e σ (λ v σ, φ v)  ∧  bounded_time e σ m
      else
        nadequate NotStuck (max_tr-1) e σ (λ v, φ v).
  Proof.
    intros Hφ Imax_tr Hspec HpreG σ.
    apply (tctr_sound (Σ:=Σ) max_tr) ; try assumption.
    intros HtcHeapG.
    iIntros "#Htickinv !#" (Φ) "Htc Post".
    wp_apply (Hspec with "Htickinv Htc"). iIntros (v Hv).
    iApply ("Post" with "[%]").
    by apply closure_free_predicate.
  Qed.

End Soundness.
