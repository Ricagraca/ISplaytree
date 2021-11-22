From iris Require Export  algebra.auth algebra.numbers.
From iris Require Import  algebra.excl base_logic.lib.own proofmode.proofmode.

Section Auth_max_nat.
  Context `{inG Σ (authR max_natUR)}.

  Lemma auth_max_nat_alloc (n : nat) :
    ⊢ |==> ∃ γ, own γ (● MaxNat n) ∗ own γ (◯ MaxNat n).
  Proof.
    iMod (own_alloc (● MaxNat n ⋅ ◯ MaxNat n)) as (γ) "[? ?]".
    - by apply auth_both_valid_2.
    - by auto with iFrame.
  Qed.

  Lemma own_auth_max_nat_le (γ : gname) (m n : nat) :
    own γ (● MaxNat m) -∗
    own γ (◯ MaxNat n) -∗
    ⌜(n ≤ m)%nat⌝.
  Proof.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as % [?%max_nat_included _] % auth_both_valid_discrete.
    iPureIntro. assumption.
  Qed.

  Lemma own_auth_max_nat_weaken (γ : gname) (n₁ n₂ : nat) :
    (n₂ ≤ n₁)%nat →
    own γ (◯ MaxNat n₁) -∗
    own γ (◯ MaxNat n₂).
  Proof.
    iIntros (I) "H".
    rewrite (_ : n₁ = n₁ `max` n₂)%nat ; last lia.
    rewrite -max_nat_op auth_frag_op. iDestruct "H" as "[_$]".
  Qed.
  Global Arguments own_auth_max_nat_weaken _ (_ _ _)%nat_scope.

  Lemma own_auth_max_nat_zero (γ : gname) :
    ⊢ |==> own γ (◯ MaxNat 0).
  Proof.
    by apply own_unit.
  Qed.

  Lemma auth_max_nat_update_read_auth (γ : gname) (m : nat) :
    own γ (● MaxNat m) -∗
    |==> own γ (● MaxNat m) ∗ own γ (◯ MaxNat m).
  Proof.
    iIntros "H●". rewrite -own_op. iApply (own_update with "H●").
    by apply auth_update_alloc, max_nat_local_update.
  Qed.

  Lemma auth_max_nat_update_incr (γ : gname) (m k : nat) :
    own γ (● MaxNat m) -∗
    |==> own γ (● MaxNat (m + k)).
  Proof.
    iIntros "H●". iApply (own_update with "H●").
    eapply auth_update_auth, max_nat_local_update. cbn. lia.
  Qed.

  Lemma auth_max_nat_update_incr' (γ : gname) (m n k : nat) :
    own γ (● MaxNat m) -∗
    own γ (◯ MaxNat n) -∗
    |==> own γ (● MaxNat (m + k)) ∗ own γ (◯ MaxNat (n + k)).
  Proof.
    iIntros "H● H◯".
    iDestruct (own_auth_max_nat_le with "H● H◯") as %I. iClear "H◯".
    iDestruct (auth_max_nat_update_incr _ _ k with "H●") as ">H●".
    iDestruct (auth_max_nat_update_read_auth with "H●") as ">[$ H◯]".
    iApply (own_auth_max_nat_weaken with "H◯"). lia.
  Qed.

End Auth_max_nat.
