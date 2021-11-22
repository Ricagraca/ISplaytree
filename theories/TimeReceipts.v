From iris.base_logic Require Import invariants.
From iris.proofmode Require Import coq_tactics.
From iris.algebra Require Import lib.gmap_view.
From iris_time.heap_lang Require Import proofmode notation adequacy lang.
From iris_time Require Import Auth_nat Auth_max_nat Reduction Tactics.
From iris_time Require Export Simulation.

Implicit Type e : expr.
Implicit Type v : val.
Implicit Type σ : state.
Implicit Type t : list expr.
Implicit Type K : ectx heap_ectx_lang.
Implicit Type m n nmax : nat.
Implicit Type φ ψ : val → Prop.
Implicit Type Σ : gFunctors.



(*
 * Abstract interface of time receipts
 *)

(* Ideally, this would be represented as a record (or a typeclass), but it has
 * to be an Iris proposition (iProp Σ) and not a Coq proposition (Prop). *)
Definition TR_interface `{irisGS heap_lang Σ, Tick}
  (nmax : nat)
  (TR : nat → iProp Σ)
  (TRdup : nat → iProp Σ)
: iProp Σ := (
    ⌜∀ n, Timeless (TR n)⌝
  ∗ ⌜∀ n, Timeless (TRdup n)⌝
  ∗ ⌜∀ n, Persistent (TRdup n)⌝
  ∗ (∀ n, TR n ={⊤}=∗ TR n ∗ TRdup n)
  ∗ (|==> TR 0%nat)
(*   ∗ (|==> TRdup 0%nat) *)
  ∗ ⌜∀ m n, TR (m + n)%nat ≡ (TR m ∗ TR n)⌝
  ∗ ⌜∀ m n, TRdup (m `max` n)%nat ≡ (TRdup m ∗ TRdup n)⌝
(*   ∗ (TR nmax ={⊤}=∗ False) *)
  ∗ (TRdup nmax ={⊤}=∗ False)
  ∗ (∀ v n, {{{ TRdup n }}} tick v {{{ RET v ; TR 1%nat ∗ TRdup (n+1)%nat }}})
)%I.



(*
 * Prerequisites on the global monoid Σ
 *)

Class timeReceiptHeapPreG Σ := {
  timeReceiptHeapPreG_heapPreG :> heapGpreS Σ ;
  timeReceiptHeapPreG_inG1 :> inG Σ (authR natUR) ;
  timeReceiptHeapPreG_inG2 :> inG Σ (authR max_natUR) ;
}.

Class timeReceiptHeapG Σ := {
  timeReceiptHeapG_heapG :> heapGS Σ ;
  timeReceiptHeapG_inG1 :> inG Σ (authR natUR) ;
  timeReceiptHeapG_inG2 :> inG Σ (authR max_natUR) ;
  timeReceiptHeapG_loc :> TickCounter ;
  timeReceiptHeapG_name1 : gname ;
  timeReceiptHeapG_name2 : gname ;
}.

Local Notation γ1 := timeReceiptHeapG_name1.
Local Notation γ2 := timeReceiptHeapG_name2.
Local Notation ℓ := tick_counter.



(*
 * Implementation and specification of `TR` and `tick`
 *)

Definition loop : val :=
  rec: "f" <> := "f" #().

Global Instance receipts_tick `{TickCounter} : Tick :=
  generic_tick loop.

Section TickSpec.

  Context `{timeReceiptHeapG Σ} (nmax : nat).

  Definition TR (n : nat) : iProp Σ :=
    own γ1 (◯nat n).

  Definition TRdup (n : nat) : iProp Σ :=
    own γ2 (◯ MaxNat n).

  (* Note: we can avoid the update modality by redefining TR like so:
         Definition TR' n : iProp Σ := ⌜n = 0%nat⌝ ∨ TR n. *)
  Lemma zero_TR :
    ⊢ |==> TR 0.
  Proof. apply own_unit. Qed.
  Lemma TR_plus m n :
    TR (m + n) ≡ (TR m ∗ TR n)%I.
  Proof. by rewrite /TR auth_frag_op own_op. Qed.
  Lemma TR_succ n :
    TR (S n) ≡ (TR 1 ∗ TR n)%I.
  Proof. by rewrite (eq_refl : S n = 1 + n)%nat TR_plus. Qed.
  Lemma TR_weaken (n₁ n₂ : nat) :
    (n₂ ≤ n₁)%nat →
    TR n₁ -∗ TR n₂.
  Proof. apply own_auth_nat_weaken. Qed.

  Lemma TR_timeless n :
    Timeless (TR n).
  Proof. exact _. Qed.

  Global Instance into_sep_TR_plus m n : IntoSep (TR (m + n)) (TR m) (TR n).
  Proof. by rewrite /IntoSep TR_plus. Qed.
  Global Instance from_sep_TR_plus m n : FromSep (TR (m + n)) (TR m) (TR n).
  Proof. by rewrite /FromSep TR_plus. Qed.
  Global Instance into_sep_TR_succ n : IntoSep (TR (S n)) (TR 1) (TR n).
  Proof. by rewrite /IntoSep TR_succ. Qed.
  Global Instance from_sep_TR_succ n : FromSep (TR (S n)) (TR 1) (TR n).
  Proof. by rewrite /FromSep [TR (S n)] TR_succ. Qed.

  (* Note: we can avoid the update modality by redefining TRdup like so:
         Definition TRdup' n : iProp Σ := ⌜n = 0%nat⌝ ∨ TRdup n. *)
  Lemma zero_TRdup :
    ⊢ |==> TRdup 0.
  Proof. apply own_unit. Qed.
  Lemma TRdup_max m n :
    TRdup (m `max` n) ≡ (TRdup m ∗ TRdup n)%I.
  Proof. by rewrite /TRdup -own_op -auth_frag_op. Qed.
  Lemma TRdup_weaken (n₁ n₂ : nat) :
    (n₂ ≤ n₁)%nat →
    TRdup n₁ -∗ TRdup n₂.
  Proof. apply own_auth_max_nat_weaken. Qed.

  Lemma TRdup_timeless n :
    Timeless (TRdup n).
  Proof. exact _. Qed.
  Lemma TRdup_persistent n :
    Persistent (TRdup n).
  Proof. exact _. Qed.

  Global Instance into_sep_TRdup_max m n : IntoSep (TRdup (m `max` n)) (TRdup m) (TRdup n).
  Proof. by rewrite /IntoSep TRdup_max. Qed.
  Global Instance from_sep_TRdup_max m n : FromSep (TRdup (m `max` n)) (TRdup m) (TRdup n).
  Proof. by rewrite /FromSep TRdup_max. Qed.

  Definition timeReceiptN := nroot .@ "timeReceipt".

  Definition TR_invariant : iProp Σ :=
    inv timeReceiptN (∃ (n:nat), ℓ ↦ #(nmax-n-1) ∗ own γ1 (●nat n) ∗ own γ2 (● MaxNat n) ∗ ⌜(n < nmax)%nat⌝)%I.

  Lemma TR_nmax_absurd (E : coPset) :
    ↑timeReceiptN ⊆ E →
    TR_invariant -∗ TR nmax ={E}=∗ False.
  Proof.
    iIntros (?) "#Inv Hγ1◯".
    iInv timeReceiptN as (n) ">(Hℓ & Hγ1● & Hγ2● & In)" "InvClose" ; iDestruct "In" as %In.
    iDestruct (own_auth_nat_le with "Hγ1● Hγ1◯") as %In'.
    exfalso ; lia.
  Qed.
  Lemma TR_lt_nmax n (E : coPset) :
    ↑timeReceiptN ⊆ E →
    TR_invariant -∗ TR n ={E}=∗ TR n ∗ ⌜n < nmax⌝%nat.
  Proof.
    iIntros (?) "#Inv Hγ1◯".
    destruct (le_lt_dec nmax n) as [ I | I ] ; last by iFrame.
    iDestruct (TR_weaken n nmax with "Hγ1◯") as "Hγ1◯" ; first done.
    iDestruct (TR_nmax_absurd with "Inv Hγ1◯") as ">?" ; first done.
    done.
  Qed.

  Lemma TRdup_nmax_absurd (E : coPset) :
    ↑timeReceiptN ⊆ E →
    TR_invariant -∗ TRdup nmax ={E}=∗ False.
  Proof.
    iIntros (?) "#Inv Hγ2◯".
    iInv timeReceiptN as (n) ">(Hℓ & Hγ1● & Hγ2● & In)" "InvClose" ; iDestruct "In" as %In.
    iDestruct (own_auth_max_nat_le with "Hγ2● Hγ2◯") as %In'. exfalso ; lia.
  Qed.
  Lemma TRdup_lt_nmax n (E : coPset) :
    ↑timeReceiptN ⊆ E →
    TR_invariant -∗ TRdup n ={E}=∗ TRdup n ∗ ⌜n < nmax⌝%nat.
  Proof.
    iIntros (?) "#Inv Hγ1◯".
    destruct (le_lt_dec nmax n) as [ I | I ] ; last by iFrame.
    iDestruct (TRdup_weaken n nmax with "Hγ1◯") as "Hγ1◯" ; first done.
    iDestruct (TRdup_nmax_absurd with "Inv Hγ1◯") as ">?" ; first done.
    done.
  Qed.

  Lemma TR_TRdup (E : coPset) n :
    ↑timeReceiptN ⊆ E →
    TR_invariant -∗ TR n ={E}=∗ TR n ∗ TRdup n.
  Proof.
    iIntros (?) "#Inv Hγ1◯".
    iInv timeReceiptN as (m) ">(Hℓ & Hγ1● & Hγ2● & Im)" "InvClose".
    iDestruct (own_auth_nat_le with "Hγ1● Hγ1◯") as %In.
    iDestruct (auth_max_nat_update_read_auth with "Hγ2●") as ">[Hγ2● Hγ2◯]".
    iAssert (TR n ∗ TRdup n)%I with "[$Hγ1◯ Hγ2◯]" as "$". {
      rewrite (_ : m = m `max` n)%nat ; last lia.
      iDestruct "Hγ2◯" as "[_ $]".
    }
    iApply "InvClose". auto with iFrame.
  Qed.

  Theorem loop_spec s E (Φ : val → iProp Σ) :
    ⊢ WP loop #() @ s ; E {{ Φ }}.
  Proof.
    iLöb as "IH". wp_rec. iExact "IH".
  Qed.

  Theorem tick_spec s E (v : val) m :
    ↑timeReceiptN ⊆ E →
    TR_invariant -∗
    {{{ TRdup m }}} tick v @ s ; E {{{ RET v ; TR 1 ∗ TRdup (m+1) }}}.
  Proof.
    intros ?. iIntros "#Inv" (Ψ) "!# Hγ2◯ HΨ".
    iLöb as "IH".
    wp_lam.
    (* open the invariant, in order to read the value k = nmax−n−1 of location ℓ: *)
    wp_bind (! _)%E ;
    iInv timeReceiptN as (n) ">(Hℓ & Hγ1● & Hγ2● & In)" "InvClose" ; iDestruct "In" as %In.
    wp_load.
    (* close the invariant: *)
    iMod ("InvClose" with "[ Hℓ Hγ1● Hγ2● ]") as "_" ; [ by auto with iFrame | iModIntro ].
    wp_let.
    (* test whether k ≤ 0: *)
    wp_op ; destruct (bool_decide (nmax - n - 1 ≤ 0)) eqn:Im ; wp_if.
    (* — if k ≤ 0 then we loop indefinitely, which gives us any spec we want
         (because we are reasoning in partial correctness): *)
    - iApply loop_spec.
    (* — otherwise: *)
    - apply Is_true_false in Im ; rewrite -> bool_decide_spec in Im.
      wp_op.
      (* open the invariant again, in order to perform CAS on location ℓ: *)
      wp_bind (CAS _ _ _)%E ;
      iInv timeReceiptN as (n') ">(Hℓ & Hγ1● & Hγ2● & In')" "InvClose" ; iDestruct "In'" as %In'.
      (* test whether the value ℓ is still k, by comparing n with n': *)
      destruct (nat_eq_dec n n') as [ <- | Hneq ].
      (* — if it holds, then CAS succeeds and ℓ is decremented: *)
      + wp_cas_suc.
        (* reform the invariant with n+1 instead of n, and an additional time
           receipt produced: *)
        replace (nmax - n - 1 - 1) with (nmax - (n+1)%nat - 1) by lia.
        iMod (auth_nat_update_incr _ _ 1 with "Hγ1●") as "[Hγ1● Hγ1◯]".
        iMod (auth_max_nat_update_incr' _ _ _ 1 with "Hγ2● Hγ2◯") as "[Hγ2● Hγ2◯]".
        assert ((n+1) < nmax)%nat by lia.
        (* close the invariant: *)
        iMod ("InvClose" with "[ Hℓ Hγ1● Hγ2● ]") as "_" ; [ by auto with iFrame | iModIntro ].
        (* finish: *)
        wp_if. iApply "HΨ" ; by iFrame.
      (* — otherwise, CAS fails and ℓ is unchanged: *)
      + wp_cas_fail ; first (injection ; lia).
        (* close the invariant as is: *)
        iMod ("InvClose" with "[ Hℓ Hγ1● Hγ2● ]") as "_" ; [ by auto with iFrame | iModIntro ] ; clear dependent n.
        wp_if.
        (* conclude using the induction hypothesis: *)
        iApply ("IH" with "Hγ2◯ HΨ").
  Qed.

  Theorem tick_spec_simple v n :
    TR_invariant -∗
    {{{ TRdup n }}} tick v {{{ RET v ; TR 1 ∗ TRdup (n+1) }}}.
  Proof.
    iIntros "#Inv" (Ψ) "!# H HΨ".
    by iApply (tick_spec with "Inv H HΨ").
  Qed.

  Lemma TR_implementation : TR_invariant -∗ TR_interface nmax TR TRdup.
  Proof.
    iIntros "#Hinv". repeat iSplitR.
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

End TickSpec.



(*
 * Soundness
 *)

Section Soundness.

  Definition adequate_trtranslation__nadequate := adequate_translation__nadequate loop.

  (* derive the adequacy of the translated program from a Hoare triple in Iris. *)

  Lemma spec_trtranslation__adequate_translation {Σ} nmax ψ e :
    (0 < nmax)%nat →
    (∀ `{timeReceiptHeapG Σ},
      TR_invariant nmax -∗
      {{{ True }}} «e» {{{ v, RET v ; ⌜ψ v⌝ }}}
    ) →
    ∀ `{timeReceiptHeapPreG Σ, TickCounter} σ,
      adequate NotStuck «e» S«σ,nmax-1» (λ v σ, ψ v).
  Proof.
    intros Inmax Hspec HpreG Hloc σ.
    (* apply the adequacy results. *)
    apply (wp_adequacy _ _) ; simpl ; intros HinvG κ.
    (* … now we have to prove a WP. *)
    set σ' := S«σ».
    (* allocate the heap, including cell ℓ (on which we need to keep an eye): *)
    iMod (gen_heap_init (<[ℓ := #(nmax-1)%nat]> σ')) as (Hheap) "(Hh● & Hℓ◯ & _)".
    iDestruct (big_sepM_lookup _ _ ℓ with "Hℓ◯") as "Hℓ◯".
    { by rewrite lookup_insert. }
    (* allocate the ghost state associated with ℓ: *)
    iMod (auth_nat_alloc 0) as (γ1) "[Hγ1● _]".
    iMod (auth_max_nat_alloc 0) as (γ2) "[Hγ2● _]".
    (* packing all those bits, build the heap instance necessary to use time receipts: *)
    pose (Build_timeReceiptHeapG Σ (HeapGS Σ _ Hheap) _ _ _ γ1 γ2)
      as HtrHeapG.
    (* create the invariant: *)
    iAssert (|={⊤}=> TR_invariant nmax)%I with "[Hℓ◯ Hγ1● Hγ2●]" as "> Hinv".
    {
      iApply inv_alloc.
      iExists 0%nat. rewrite (_ : nmax - 0 - 1 = Z.of_nat (nmax - 1)) ; last lia.
      by iFrame.
    }
    iModIntro.
    (* finally, use the user-given specification: *)
    iExists (λ σ _, gen_heap_interp σ), (λ _, True%I). iFrame.
    iApply (Hspec with "Hinv") ; auto.
  Qed.

  Theorem spec_trtranslation__nadequate {Σ} nmax φ e :
    (0 < nmax)%nat →
    (∀ `{timeReceiptHeapG Σ},
      TR_invariant nmax -∗
      {{{ True }}} «e» {{{ v, RET v ; ⌜φ (invtranslationV v)⌝ }}}
    ) →
    ∀ `{!timeReceiptHeapPreG Σ} σ,
      nadequate NotStuck (nmax-1) e σ φ.
  Proof.
    intros Inmax Hspec HpreG σ.
    eapply adequate_trtranslation__nadequate.
    intros Hloc. by eapply spec_trtranslation__adequate_translation.
  Qed.

  Theorem abstract_spec_trtranslation__nadequate {Σ} nmax φ e :
    (0 < nmax)%nat →
    (∀ `{heapGS Σ, Tick} (TR TRdup : nat → iProp Σ),
      TR_interface nmax TR TRdup -∗
      {{{ True }}} «e» {{{ v, RET v ; ⌜φ (invtranslationV v)⌝ }}}
    ) →
    ∀ {_ : timeReceiptHeapPreG Σ} σ,
      nadequate NotStuck (nmax-1) e σ φ.
  Proof.
    intros Inmax Hspec HpreG σ.
    eapply spec_trtranslation__nadequate; try done.
    clear HpreG. iIntros (HtrHeapG) "#Hinv".
    iApply Hspec. by iApply TR_implementation.
  Qed.

End Soundness.

(*
 * Proof-mode tactics for proving WP of translated expressions
 *)

Lemma tac_wp_tick `{timeReceiptHeapG Σ} Δ pe Δ1 Δ2 Δ' i max_tc s E K (v : val) Φ :
  ↑timeReceiptN ⊆ E →
  MaybeIntoLaterNEnvs 1 Δ Δ1 →

  envs_lookup i Δ = Some (pe, TR_invariant max_tc) →

  (∃ j pe' p, envs_lookup j Δ1 = Some (pe', TRdup p) ∧
              envs_simple_replace j pe' (Esnoc Enil j (TRdup (S p))) Δ1 = Some Δ2) ∨
  Δ1 = Δ2 →

  (∃ j n, envs_lookup j Δ2 = Some (false, TR n) ∧
          envs_simple_replace j false (Esnoc Enil j (TR (S n))) Δ2 = Some Δ') ∨
  Δ2 = Δ' →

  envs_entails Δ' (WP fill K v @ s; E {{ Φ }}) →
  envs_entails Δ (WP fill K (App tick v) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=>??? HTRdup HTR HWP.
  iIntros "HΔ".
  iAssert (TR_invariant max_tc) as "#Hinv".
  { destruct pe.
    iDestruct (envs_lookup_sound _ i true with "HΔ") as "[? _]"=>//.
    iDestruct (envs_lookup_sound _ i false with "HΔ") as "[? _]"=>//. }
  iDestruct (into_laterN_env_sound with "HΔ") as "HΔ1"=>//.
  iApply wp_bind.
  destruct HTR as [(j & n & HTR1 & HTR2)| ->],
           HTRdup as [(j' & pe'' & p & HTRDup1 & HTRDup2)| ->].
  - iDestruct (envs_simple_replace_singleton_sound with "HΔ1") as "[HTRdup HΔ2]"=>//.
    rewrite bi.intuitionistically_if_elim -bi.intuitionistically_intuitionistically_if.
    iDestruct "HTRdup" as "#>HTRdup".
    iApply (tick_spec with "[//] HTRdup")=>//. iIntros "!> [HTR #HTRdup']". iApply HWP.
    rewrite Nat.add_comm. iSpecialize ("HΔ2" with "[//]").
    iDestruct (envs_simple_replace_singleton_sound with "HΔ2") as "[HTR' HΔ']"=>//=.
    iCombine "HTR HTR'" as "HTR". iDestruct ("HΔ'" with "HTR") as "$".
  - iMod zero_TRdup as "HTRdup".
    iApply (tick_spec with "[//] HTRdup")=>//. iIntros "!> [HTR _]". iApply HWP.
    iDestruct (envs_simple_replace_singleton_sound with "HΔ1") as "[HTR' HΔ']"=>//=.
    iCombine "HTR HTR'" as "HTR". iDestruct ("HΔ'" with "HTR") as "$".
  - iDestruct (envs_simple_replace_singleton_sound with "HΔ1") as "[HTRdup HΔ']"=>//.
    rewrite bi.intuitionistically_if_elim -bi.intuitionistically_intuitionistically_if.
    iDestruct "HTRdup" as "#>HTRdup".
    iApply (tick_spec with "[//] HTRdup")=>//. iIntros "!> [_ #HTRdup']". iApply HWP.
    rewrite Nat.add_comm. iDestruct ("HΔ'" with "[//]") as "$".
  - iMod zero_TRdup as "HTRdup".
    iApply (tick_spec with "[//] HTRdup")=>//. iIntros "!> [_ #HTRdup']". by iApply HWP.
Qed.

Ltac wp_tick ::=
  iStartProof ;
  simpl_trans ;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
      first
        [ reshape_expr false e ltac:(fun K e' =>
            eapply (tac_wp_tick _ _ _ _ _ _ _ _ _ K)
          )
        | fail 1 "wp_tick: cannot find 'tick ?v' in" e ] ;
      [ try solve_ndisj
      | exact _
      | (* lookup invariant: *) (iAssumptionCore || fail "wp_tick: cannot find TR_invariant")
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
