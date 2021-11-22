From iris.base_logic Require Import invariants.
From iris.algebra Require Import lib.gmap_view.
From iris_time.heap_lang Require Import proofmode notation adequacy lang.
From iris_time Require Import Auth_nat Reduction.
From iris_time Require Export TimeCredits.

Implicit Type e : expr.
Implicit Type v : val.
Implicit Type σ : state.
Implicit Type t : list expr.
Implicit Type K : ectx heap_ectx_lang.
Implicit Type m n : nat.
Implicit Type φ ψ : val → Prop.
Implicit Type Σ : gFunctors.

Local Notation γ := timeCreditHeapG_name.
Local Notation ℓ := tick_counter.

(* In general, one can prove:
 *     if the translated program with the counter initialized to m is safe,
 *     then the source program is m-safe.
 * This is lemma [adequate_translation__nadequate] in `Simulation.v`.
 *
 * Moreover, for time credits, we can prove:
 *     if the translated program with the counter initialized to m is safe,
 *     then the source program computes in at most m steps.
 * This is lemma [safe_tctranslation__bounded] in `TimeCredits.v` (it relies
 * crucially on the unsafe behavior of “tick” for time credits).
 *
 * However, the combination of both results does not imply that the source
 * program is safe, because m-safety only describe sequences of reductions of
 * length strictly less than m, so we cannot tell what happens for sequences
 * of length exactly m.
 *
 * In `TimeCredits.v`, this is solved by proving that (roughly):
 *     if the Hoare triple  { TC m } «e» { φ }  holds,
 *     then FOR ALL m' ≥ m,
 *       the translated program with the counter initialized to m' is safe.
 * This is lemma [spec_tctranslation__adequate_translation] in `TimeCredits.v`.
 *
 * Hence from the Hoare triple we can deduce that the source program
 *   (1)  computes in at most m steps (by taking m' = m), and
 *   (2)  is (m+1)-safe (by taking m' = m+1),
 * which is enough to conclude that it is completely safe.
 *
 * However, this is not completely natural, because deducing (2) amounts to
 * giving the translated program one credit more than required.
 *
 * In fact, exploiting the unsafe behavior of “tick”, we can prove that:
 *     if the translated program with the counter initialized to m is safe,
 *     then the source program is safe.
 * The proof is given below. It is mostly a copy-paste of the general proof
 * of [adequate_translation__nadequate] in `Simulation.v`, with additional calls
 * to [safe_tctranslation__bounded] and one call to [not_safe_tick].
 *)

(* assuming the safety of the translated expression,
 * a proof that the original expression is safe. *)

Lemma safe_tctranslation__safe_here {Hloc : TickCounter} m e σ :
  loc_fresh_in_expr ℓ e →
  safe «e» S«σ, m» →
  is_Some (to_val e) ∨ reducible e σ.
Proof.
  intros Hfresh Hsafe.
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
        destruct m as [ | m ] ; first (exfalso ; eapply not_safe_tick, Hsafe).
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
Lemma safe_tctranslation__safe {Hloc : TickCounter} m e σ t2 σ2 e2 :
  loc_fresh_in_expr ℓ e2 →
  σ2 !! ℓ = None →
  safe «e» S«σ, m» →
  rtc erased_step ([e], σ) (t2, σ2) →
  e2 ∈ t2 →
  is_Some (to_val e2) ∨ reducible e2 σ2.
Proof.
  intros Hℓe Hℓσ Hsafe [n Hnsteps] % rtc_nsteps He2.
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

Lemma adequate_tctranslation__adequate_result {Hloc : TickCounter} m φ e σ t2 σ2 v2 :
  σ2 !! ℓ = None →
  adequate NotStuck «e» S«σ, m» (λ v σ, φ (invtranslationV v)) →
  rtc erased_step ([e], σ) (Val v2 :: t2, σ2) →
  φ v2.
Proof.
  intros Hfresh Hadq [n Hnsteps] % rtc_nsteps.
  assert (safe «e» S«σ, m») as Hsafe by by eapply safe_adequate.
  assert (n ≤ m)%nat by by eapply safe_tctranslation__bounded.
  replace (φ v2) with ((φ ∘ invtranslationV) (translationV v2))
    by (simpl ; by rewrite invtranslationV_translationV).
  eapply (adequate_result _ _ _ (λ v σ, φ (invtranslationV v))) ; first done.
  change [«e»%E] with T«[e]».
  replace (Val «v2» :: _) with (T«Val v2 :: t2») by done.
  eapply simulation_exec_success' ; eauto.
Qed.

(* now let’s combine the two results. *)

Lemma adequate_tctranslation__adequate m φ e σ :
  (∀ `{TickCounter}, adequate NotStuck «e» S«σ, m» (λ v σ, φ (invtranslationV v))) →
  adequate NotStuck e σ (λ v σ, φ v).
Proof.
  intros Hadq.
  split.
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
Qed.



(* On the contrary, it is possible to get rid of the dependency upon the unsafe
 * behavior of “tick”.
 *
 * The fact that, for time credits, “tick” crashes when the counter is depleted,
 * is essential to prove the operational version of the main result: that the
 * safety of a translated program implies an upper bound on the running time of
 * the source program (lemma [safe_tctranslation__bounded] in `TimeCredits.v`).
 *
 * However, it is redundant from the logical point of view: because we give a
 * time credit to “tick” (in its Hoare specification [tick_spec]), the counter
 * is guaranteed not to be exhausted, and the crashing branch is dead code.
 *
 * Hence we may as well implement “tick” with a mere decrementation, whatever
 * the value of the counter is. If we do so, then we can strenghten the
 * simulation lemma as such:
 *     if (t₁, σ₁) reduces to (t₂, σ₂) in n steps,
 *     then for all (relative) integer m,
 *       («t₁», «σ₁»[ℓ:=m]) reduces to («t₂», «σ₂»[ℓ:=m−n]).
 * In other words, there is no need anymore for the initial value m of the
 * counter to be at least equal to n.
 *
 * Then, for that modified implementation of “tick”, we can prove:
 *     if the Hoare triple  { TC m } «e» { φ }  holds,
 *     then the source program computes in at most m steps.
 *
 * Whereas the proof which relies on the crashing behavior uses [wp_adequacy]
 * (the fact that the WP predicate is sound, that is, implies the safety/adequacy
 * of the program), this proof uses [wp_invariance] instead (the fact that the
 * WP predicate preserves invariants of the program).
 *
 * The idea of the proof is as follows: given a n-step reduction from (t₁, σ₁)
 * to (t₂, σ₂), the strenghtened simulation lemma gives a reduction from
 * («t₁», «σ₁»[ℓ:=m]) to («t₂», «σ₂»[ℓ:=m−n]). The invariant of time credits
 * in the final state implies that m−n is a non-negative integer; otherwise
 * said, n ≤ m.
 *)

Lemma spec_tctranslation__bounded {Σ} m ψ e :
  (∀ `{timeCreditHeapG Σ},
    TC_invariant -∗
    {{{ TC m }}} «e» {{{ v, RET v ; ⌜ψ v⌝ }}}
  ) →
  ∀ `{TickCounter} `{timeCreditHeapPreG Σ} σ1 t2 σ2 (z : Z),
    rtc erased_step ([«e»], S«σ1, m») (T«t2», S«σ2, z») →
    0 ≤ z.
Proof.
  intros Hspec Hloc HtcPreG σ1 t2 σ2 z Hsteps.
  (* apply the invariance result. *)
  apply (wp_invariance Σ _ NotStuck «e» S«σ1,m» T«t2» S«σ2,z») ; simpl ; last assumption.
  intros HinvG κs(*κs'*).
  (* … now we have to prove a WP for some state interpretation, for which
   * we settle the needed invariant TC_invariant. *)
  set σ' := S«σ1».
  (* allocate the heap, including cell ℓ (on which we need to keep an eye): *)
  iMod (gen_heap_init (<[ℓ := #m]> σ')) as (Hheap) "(Hh● & Hℓ◯ & _)".
  iDestruct (big_sepM_lookup _ _ ℓ with "Hℓ◯") as "Hℓ◯".
  { by rewrite lookup_insert. }
  (* allocate the ghost state associated with ℓ: *)
  iMod (auth_nat_alloc m) as (γ) "[Hγ● Hγ◯]".
  (* packing all those bits, build the heap instance necessary to use time credits: *)
  destruct HtcPreG as [[HinvPreG [HgenHeapPreInG]] HinG] ; simpl ; clear HinvPreG.
  pose (Build_timeCreditHeapG Σ (HeapGS Σ HinvG Hheap) HinG _ γ)
    as HtcHeapG.
  (* create the invariant: *)
  iAssert (|={⊤}=> TC_invariant)%I with "[Hℓ◯ Hγ●]" as "> #Hinv".
  {
    iApply inv_alloc.
    iExists m. by iFrame.
  }
  (* finally, use the user-given specification: *)
  iModIntro.
    iExists (λ σ _ _, gen_heap_interp σ), (λ _, True%I). iFrame.
  iSplitL ; first (iApply (Hspec with "Hinv Hγ◯") ; auto).
  (* it remains to prove that the interpretation of the final state, along
   * with the invariant, implies the inequality… *)
  iIntros "Hheap2". iExists _.
  (* open the invariant: *)
  iInv timeCreditN as (m') ">[Hc Hγ●]" "InvClose".
  (* derive that z = m' (that is, the relative integer is in fact a natural integer): *)
  iDestruct (gen_heap_valid with "Hheap2 Hc") as %Eq.
  rewrite lookup_insert in Eq.
  injection Eq as ->.
  (* close the invariant (in fact, this is not required), and conclue: *)
  iMod ("InvClose" with "[-]") as "_" ; by auto with iFrame lia.
Qed.

(* The simulation lemma with no assumption that m ≤ n. *)
Axiom simulation_exec_alt : ∀ {Hloc : TickCounter} m n t1 σ1 t2 σ2,
  σ2 !! ℓ = None →
  relations.nsteps erased_step m (t1, σ1) (t2, σ2) →
  rtc erased_step (T«t1», S«σ1, n») (T«t2», S«σ2, (n-m)%Z»).

Lemma spec_tctranslation__bounded' {Σ} m ψ e :
  (∀ `{timeCreditHeapG Σ},
    TC_invariant -∗
    {{{ TC m }}} «e» {{{ v, RET v ; ⌜ψ v⌝ }}}
  ) →
  ∀ `{!timeCreditHeapPreG Σ} σ,
    bounded_time e σ m.
Proof.
  intros Hspec HtcPreG σ t2 σ2 n Hnsteps.
  (* build a location ℓ which is not in the domain of σ2: *)
  pose (Build_TickCounter (fresh (dom (gset loc) σ2))) as Hloc.
  assert (σ2 !! ℓ = None)
    by (unfold ℓ ; eapply (not_elem_of_dom (D:=gset loc)), is_fresh).
  eapply simulation_exec_alt in Hnsteps ; auto.
  assert (0 ≤ m-n)%Z by by eapply spec_tctranslation__bounded.
  lia.
Qed.
