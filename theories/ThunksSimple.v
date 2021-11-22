From stdpp Require Import namespaces.
From iris.base_logic.lib Require Import na_invariants.
From iris_time.heap_lang Require Import proofmode notation.
From iris_time Require Import TimeCredits Auth_max_nat.

(* This file contains a simple formalization of thunks, as presented in the
   ESOP 2019 paper. It does not enjoy the consequence rule. A more elaborate
   formalization (with the same HeapLang code) can be found in Thunks.v. *)

Notation UNEVALUATED f := (InjL f%V) (only parsing).
Notation EVALUATED v := (InjR v%V) (only parsing).
Notation UNEVALUATEDV f := (InjLV f%V) (only parsing).
Notation EVALUATEDV v := (InjRV v%V) (only parsing).
Notation "'match:' e0 'with' 'UNEVALUATED' x1 => e1 | 'EVALUATED' x2 => e2 'end'" :=
  (Match e0 x1%bind e1 x2%bind e2)
  (e0, e1, x2, e2 at level 200, only parsing) : expr_scope.

Definition create : val :=
  λ: "f",
    ref (UNEVALUATED "f").

Definition force : val :=
  λ: "t",
    match: ! "t" with
      UNEVALUATED "f" =>
        let: "v" := "f" #() in
        "t" <- (EVALUATED "v") ;;
        "v"
    | EVALUATED "v" =>
        "v"
    end.

Section ThunkSimpleProofs.

  Context `{timeCreditHeapG Σ}.
  Context `{inG Σ (authR max_natUR)}.
  Context `{na_invG Σ}.

  Implicit Type t : loc.
  Implicit Type γ : gname.
  Implicit Type n nc ac : nat.
  Implicit Type φ : val → iProp Σ.
  Implicit Type f v : val.
  Implicit Type p : na_inv_pool_name.
  Implicit Type E F : coPset.

  Definition thunkN t : namespace :=
    nroot .@ "thunk" .@ string_of_pos t.

  Definition ThunkInv t γ nc φ : iProp Σ := (
    ∃ (ac : nat),
        own γ (● MaxNat ac)
      ∗ (
          (∃ (f : val),
              t ↦ UNEVALUATEDV « f »
            ∗ {{{ TC nc }}} « f #() » {{{ v, RET « v » ; φ v }}}
            ∗ TC ac
          )
        ∨ (∃ (v : val),
              t ↦ EVALUATEDV « v »
            ∗ φ v
          )
        )
  )%I.
  Definition Thunk p t n φ : iProp Σ := (
    ∃ (γ : gname) (nc : nat),
        na_inv p (thunkN t) (ThunkInv t γ nc φ)
      ∗ own γ (◯ MaxNat (nc-n))
  )%I.

  Lemma thunk_persistent p t n φ :
    Persistent (Thunk p t n φ).
  Proof. exact _. Qed.

  Lemma thunk_dup p t n φ :
    Thunk p t n φ ≡ (Thunk p t n φ ∗ Thunk p t n φ)%I.
  Proof.
    iSplit. { auto. } { iIntros "[$_]". }
  Qed.

  Lemma Thunk_weaken p t n₁ n₂ φ :
    (n₁ ≤ n₂)%nat →
    Thunk p t n₁ φ -∗
    Thunk p t n₂ φ.
  Proof.
    iIntros (I) "H". iDestruct "H" as (γ nc) "[Hinv Hγ◯]".
    iExists γ, nc. iFrame "Hinv".
    iDestruct (own_auth_max_nat_weaken _ (nc-n₁) (nc-n₂) with "Hγ◯") as "$". lia.
  Qed.

  Lemma create_spec p nc φ f :
    TC_invariant -∗
    {{{ TC 3 ∗ ( {{{ TC nc }}} «f #()» {{{ v, RET « v » ; φ v }}} ) }}}
    «create f»
    {{{ (t : loc), RET #t ; Thunk p t nc φ }}}.
  Proof.
    iIntros "#Htickinv" (Φ) "!# [? Hf] Post".
    iMod (auth_max_nat_alloc 0) as (γ) "[Hγ● Hγ◯]".
    iApply wp_fupd.
    wp_tick_lam. wp_tick_inj. wp_tick_alloc t.
    iApply "Post".
    iExists γ, nc ; rewrite (_ : nc - nc = 0)%nat ; last lia.
    iFrame "Hγ◯".
    iApply na_inv_alloc.
    iNext. iExists 0%nat. auto with iFrame.
  Qed.

  Lemma force_spec p F t φ :
    ↑(thunkN t) ⊆ F →
    (∀ (v : val), φ v -∗ φ v ∗ φ v) →
    TC_invariant -∗
    {{{ TC 11 ∗ Thunk p t 0 φ ∗ na_own p F }}}
    «force #t»
    {{{ v, RET «v» ; φ v ∗ na_own p F }}}.
  Proof.
    iIntros (? Hφdup).
    iIntros "#Htickinv" (Φ) "!# (? & #Hthunk & Hp) Post".
    iDestruct "Hthunk" as (γ nc) "#[Hthunkinv Hγ◯]".
    rewrite (_ : nc - 0 = nc)%nat ; last lia.
    iApply wp_fupd.
    wp_tick_lam.
    (* reading the thunk… *)
    iDestruct (na_inv_acc p ⊤ F (thunkN t) with "Hthunkinv Hp")
      as ">(Hthunk & Hp & Hclose)" ; [done|done|] ;
      iDestruct "Hthunk" as (ac) "(>Hγ● & [ Hunevaluated | Hevaluated ])" ;
      [ iDestruct "Hunevaluated" as (f) "(>Ht & Hf & >Htc)"
      | iDestruct "Hevaluated" as (v) "(>Ht & Hv)" ].
    (* (1) if it is UNEVALUATED, we evaluate it: *)
    {
      wp_tick_load. wp_tick_match.
      iDestruct (own_auth_max_nat_le with "Hγ● Hγ◯") as %I.
      iDestruct (TC_weaken _ _ I with "Htc") as "Htc".
      wp_apply ("Hf" with "Htc") ; iIntros (v) "Hv".
      wp_tick_let. wp_tick_inj. wp_tick_store. wp_tick_seq.
      iApply "Post".
      iDestruct (Hφdup with "Hv") as "[Hv $]".
      iApply "Hclose". iFrame "Hp".
      iNext. iExists ac. auto with iFrame.
    }
    (* (2) if it is EVALUATED, we get the result which is already memoized: *)
    {
      wp_tick_load. wp_tick_match.
      iApply "Post".
      iDestruct (Hφdup with "Hv") as "[Hv $]".
      iApply "Hclose". iFrame "Hp".
      iNext. iExists ac. auto with iFrame.
    }
  Qed.

  Lemma pay_spec p F (n k : nat) t φ :
    ↑(thunkN t) ⊆ F →
    na_own p F -∗ Thunk p t n φ -∗ TC k ={⊤}=∗ Thunk p t (n-k) φ ∗ na_own p F.
  Proof.
    iIntros (?) "Hp #Hthunk Htc_k".
    iDestruct "Hthunk" as (γ nc) "#[Hthunkinv Hγ◯]".
    (* reading the thunk… *)
    iDestruct (na_inv_acc p ⊤ F (thunkN t) with "Hthunkinv Hp")
      as ">(Hthunk & Hp & Hclose)" ; [done|done|] ;
      iDestruct "Hthunk" as (ac) "(>Hγ● & [ Hunevaluated | Hevaluated ])" ;
      [ iDestruct "Hunevaluated" as (f) "(>Ht & Hf & >Htc)"
      | iDestruct "Hevaluated" as (v) "(>Ht & Hv)" ].
    (* (1) if it is UNEVALUATED, then we add the time credits to the deposit: *)
    {
      iAssert (TC (ac + k)) with "[Htc Htc_k]" as "Htc" ;
        first by iSplitL "Htc".
      iDestruct (auth_max_nat_update_incr' _ _ _ k with "Hγ● Hγ◯") as ">[Hγ●' #Hγ◯']" ;
        iClear "Hγ◯".
      iMod ("Hclose" with "[-Hγ◯']") as "$". {
        iFrame "Hp".
        iNext. iExists (ac+k)%nat. auto with iFrame.
      }
      iModIntro.
      iExists γ, nc. iFrame "Hthunkinv".
      iDestruct (own_auth_max_nat_weaken _ ((nc-n)+k) (nc-(n-k)) with "Hγ◯'") as "$" ; lia.
    }
    (* (2) if it is EVALUATED, then we do nothing: *)
    {
      iDestruct (auth_max_nat_update_incr' _ _ _ k with "Hγ● Hγ◯") as ">[Hγ●' #Hγ◯']" ;
        iClear "Hγ◯".
      iMod ("Hclose" with "[-Hγ◯']") as "$". {
        iFrame "Hp".
        iNext. iExists (ac+k)%nat. auto with iFrame.
      }
      iModIntro.
      iExists γ, nc. iFrame "Hthunkinv".
      iDestruct (own_auth_max_nat_weaken _ ((nc-n)+k) (nc-(n-k)) with "Hγ◯'") as "$" ; lia.
    }
  Qed.

End ThunkSimpleProofs.
