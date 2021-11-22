From iris Require Export  algebra.auth algebra.numbers.
From iris Require Import  base_logic.lib.own proofmode.proofmode.

Notation "'●nat' n" := (auth_auth (A:=natUR) (DfracOwn 1%Qp) n%nat) (at level 20).
Notation "'◯nat' n" := (auth_frag (A:=natUR) n%nat) (at level 20).

Section Auth_nat.
  Context `{inG Σ (authR natUR)}.

  Lemma auth_nat_alloc (n : nat) :
    ⊢ |==> ∃ γ, own γ (●nat n) ∗ own γ (◯nat n).
  Proof.
    iMod (own_alloc (●nat n ⋅ ◯nat n)) as (γ) "[? ?]".
    - by apply auth_both_valid_2.
    - by auto with iFrame.
  Qed.

  Lemma own_auth_nat_le (γ : gname) (m n : nat) :
    own γ (●nat m) -∗
    own γ (◯nat n) -∗
    ⌜(n ≤ m)%nat⌝.
  Proof.
    iIntros "H● H◯".
    by iDestruct (own_valid_2 with "H● H◯")
      as % [?%nat_le_sum _] % auth_both_valid.
  Qed.

  Lemma own_auth_nat_weaken (γ : gname) (n₁ n₂ : nat) :
    (n₂ ≤ n₁)%nat →
    own γ (◯nat n₁) -∗
    own γ (◯nat n₂).
  Proof.
    iIntros (I) "H".
    rewrite (_ : n₁ = (n₁ - n₂) + n₂)%nat ; last lia.
    iDestruct "H" as "[_$]".
  Qed.

  Lemma own_auth_nat_zero (γ : gname) :
    ⊢ |==> own γ (◯nat 0).
  Proof.
    apply own_unit.
  Qed.

  Lemma auth_nat_update_incr (γ : gname) (m k : nat) :
    own γ (●nat m) -∗
    |==> own γ (●nat (m + k)) ∗ own γ (◯nat k).
  Proof.
    iIntros "H●".
    rewrite -own_op. iApply (own_update with "H●").
    apply auth_update_alloc, nat_local_update. rewrite right_id. lia.
  Qed.

  Lemma auth_nat_update_decr (γ : gname) (m n k : nat) :
    (k ≤ n)%nat →
    own γ (●nat m) -∗
    own γ (◯nat n) -∗
    |==> own γ (●nat (m - k)) ∗ own γ (◯nat (n - k)).
  Proof.
    iIntros (I) "H● H◯".
    iDestruct (own_auth_nat_le with "H● H◯") as %J.
    rewrite -own_op. iApply (own_update_2 with "H● H◯").
    apply auth_update, nat_local_update. lia.
  Qed.
End Auth_nat.
