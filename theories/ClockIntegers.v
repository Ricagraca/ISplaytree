From stdpp Require Import numbers.
From iris_time.heap_lang Require Import proofmode notation.
From iris_time Require Import TimeReceipts.

Open Scope Z_scope.

(*
 * A “clock integer” (“onetime integer” in Clochard’s thesis) is a non-duplicable
 * integer which supports addition.
 *)

Section clock_int.
  Context `{timeReceiptHeapG Σ}.
  Context (nmax : nat).
  Context `(nmax ≤ max_mach_int).

  Definition is_clock_int (n : Z) : iProp Σ :=
    (⌜0 ≤ n⌝ ∗ TR (Z.to_nat n))%I.

  (* Clock integers support addition, which consumes its arguments: *)
  Lemma clock_int_add_spec (n1 n2 : mach_int) :
    TR_invariant nmax -∗
    {{{ is_clock_int (`n1) ∗ is_clock_int (`n2) }}}
    «#n1 + #n2»
    {{{ H, RET #(LitMachInt ((`n1+`n2) ↾ H)) ; is_clock_int (`n1+`n2) }}}.
  Proof.
    iIntros "#Htrinv" (Φ) "!# ([% H1] & [% H2]) Post".
    iAssert (TR (Z.to_nat (`n1+`n2))) with "[H1 H2]" as "H".
    { rewrite Z2Nat.inj_add // TR_plus. iFrame. }
    iDestruct (TR_lt_nmax with "Htrinv H") as ">(H & Hnmax)" ; [done|].
    iDestruct "Hnmax" as %Hnmax.
    assert (`n1 + `n2 < max_mach_int).
    { rewrite -(Nat2Z.id nmax) in Hnmax. apply Z2Nat.inj_lt in Hnmax; lia. }
    assert (bool_decide (mach_int_bounded (`n1 + `n2))).
    { apply bool_decide_pack. split; [|done].
      (* FIXME : why isn't lia able to do this directly? *)
      trans 0. unfold min_mach_int; lia. lia. }
    iDestruct ("Post" with "[H]") as "Post".
    { iIntros "{$H} !%". lia. }
    wp_tick_op=>//.
    by rewrite /bin_op_eval /= /to_mach_int /mach_int_bounded decide_True_pi.
  Qed.
End clock_int.

(*
 * A “snapclock integer” (“peano integer” in Clochard’s thesis) is a duplicable
 * integer which only supports incrementation.
 *)

Section snapclock_int.

  Context `{timeReceiptHeapG Σ}.
  Context (nmax : nat).
  Context `(nmax < max_mach_int).

  Definition is_snapclock_int (n : Z) : iProp Σ :=
    (⌜0 ≤ n⌝ ∗ TRdup (Z.to_nat n))%I.

  (* Snapclock integers are persistent (in particular they are duplicable): *)
  Lemma snapclock_int_persistent (n : Z) :
    Persistent (is_snapclock_int n).
  Proof. exact _. Qed.

  (* Snapclock integers support incrementation: *)
  Lemma snapclock_int_incr_spec (n1 : mach_int) :
    TR_invariant nmax -∗
    {{{ is_snapclock_int (`n1) }}}
    «#n1 + #mach_int_1»
    {{{ H, RET #(LitMachInt ((`n1+1) ↾ H)) ; is_snapclock_int (`n1+1) }}}.
  Proof.
    iIntros "#Htrinv" (Φ) "!# [% H] Post".
    iDestruct (TRdup_lt_nmax with "Htrinv H") as ">(H & Hnmax)" ; first done.
    iDestruct "Hnmax" as %Hnmax.
    assert (`n1 + 1 < max_mach_int).
    { rewrite -(Nat2Z.id nmax) in Hnmax. apply Z2Nat.inj_lt in Hnmax; lia. }
    assert (bool_decide (mach_int_bounded (`n1 + 1))).
    { apply bool_decide_pack. split; [|done].
      (* FIXME : why isn't lia able to do this directly? *)
      trans 0. unfold min_mach_int; lia. lia. }
    wp_tick_op.
    { by rewrite /bin_op_eval /= /to_mach_int /mach_int_bounded decide_True_pi. }
    iApply "Post". iSplit. auto with lia.
    rewrite Z2Nat.inj_add // Nat.add_comm //.
  Qed.

  (* Snapclock integers also support a limited form of addition: *)
  Lemma snapclock_int_add_spec (n1 n2 : mach_int) (m : Z) :
    TR_invariant nmax -∗
    {{{ is_snapclock_int (`n1) ∗ is_snapclock_int (`n2)
      ∗ is_snapclock_int m ∗ ⌜`n1+`n2 ≤ m⌝ }}}
    «#n1 + #n2»
    {{{ H, RET #(LitMachInt ((`n1+`n2) ↾ H)) ; is_snapclock_int (`n1+`n2) }}}.
  Proof.
    iIntros "#Htrinv" (Φ) "!# ([% _] & [% _] & [% Hm] & %) Post".
    iDestruct (TRdup_lt_nmax with "Htrinv Hm") as ">(Hm & Hnmax)" ; first done.
    iDestruct "Hnmax" as %Hnmax.
    assert (m < max_mach_int).
    { rewrite -(Nat2Z.id nmax) in Hnmax. apply Z2Nat.inj_lt in Hnmax; lia. }
    iDestruct (TRdup_weaken (Z.to_nat m) (Z.to_nat (`n1 + `n2)) with "Hm") as "H".
    { apply Z2Nat.inj_le; lia. }
    assert (bool_decide (mach_int_bounded (`n1 + `n2))).
    { apply bool_decide_pack. split; [|lia].
      (* FIXME : why isn't lia able to do this directly? *)
      trans 0. unfold min_mach_int; lia. lia. }
    iDestruct ("Post" with "[H]") as "Post".
    { iSplit; auto with lia. }
    wp_tick_op=>//.
    by rewrite /bin_op_eval /= /to_mach_int /mach_int_bounded decide_True_pi.
  Qed.
End snapclock_int.
