From iris.program_logic Require Export weakestpre adequacy.
From iris.algebra Require Import auth.
From iris_time.heap_lang Require Import proofmode notation.
From iris.proofmode Require Import proofmode.
Set Default Proof Using "Type".

Class heapGpreS Σ := HeapGpreS {
  heap_preG_iris :> invGpreS Σ;
  heap_preG_heap :> gen_heapGpreS loc val Σ
}.

Definition heapΣ : gFunctors := #[invΣ; gen_heapΣ loc val].
Instance subG_heapPreG {Σ} : subG heapΣ Σ → heapGpreS Σ.
Proof. solve_inG. Qed.

Definition heap_adequacy Σ `{heapGpreS Σ} s e σ φ :
  (∀ `{heapGS Σ}, ⊢ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp; eapply (wp_adequacy _ _); iIntros (??) "".
  iMod (gen_heap_init σ) as (?) "[Hh _]".
  iModIntro.
  iExists (λ σ κs, (gen_heap_interp σ)%I), (λ _, True%I). iFrame.
  iApply (Hwp (HeapGS _ _ _)).
Qed.
