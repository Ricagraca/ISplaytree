From iris.program_logic Require Import adequacy.
From iris_time.heap_lang Require Import notation proofmode.
From iris_time Require Import Base Reduction Tactics.
From iris_time Require Export Translation.

Implicit Type e : expr.
Implicit Type v : val.
Implicit Type σ : state.
Implicit Type t : list expr.
Implicit Type K : ectx heap_ectx_lang.
Implicit Type ℓ : loc.
Implicit Type m n : nat.
Implicit Type φ : val → Prop.



(* Our definition of “tick” will depend on a location. This is made a typeclass
 * so as to be inferred automatically. *)
Class TickCounter := { tick_counter : loc }.
Notation "S« σ , n »" := (<[tick_counter := LitV (LitInt n%nat)]> (translationS σ%V)).
(* Notation "« σ , n »" := (<[ℓ := LitV (LitInt n%nat)]> (translationS σ%V)) (only printing). *)
Local Notation ℓ := tick_counter.


(* This whole file is parameterized by a “runtime_error” value: *)
Section Simulation.
Context (runtime_error : val).



(*
 * Definition of “tick”
 *)

Local Instance generic_tick {Hloc : TickCounter} : Tick :=
 (rec: "tick" "x" :=
    let: "k" := ! #ℓ in
    if: "k" ≤ #0 then
      runtime_error #()
    else if: CAS #ℓ "k" ("k" - #1) then
      "x"
    else
      "tick" "x")%V.


(*
 * Operational behavior of “tick”
 *)

Section Tick_exec.

  Context {Hloc : TickCounter}.

  Lemma exec_tick_success n v σ :
    prim_exec  (tick v) (<[ℓ := #(S n)]> σ)  v (<[ℓ := #n]> σ)  [].
  Proof.
    remember (Z.of_nat (S n)) as Sn.
    unlock tick generic_tick.
    eapply prim_exec_cons_nofork. (* Initial β-redex *)
    { by prim_step. }
    simpl. eapply prim_exec_cons_nofork. (* Load of ℓ *)
    { prim_step; apply lookup_insert. }
    simpl. eapply prim_exec_cons_nofork. (* First redex of let *)
    { by prim_step. }
    simpl. eapply prim_exec_cons_nofork. (* Second redex of let *)
    { by prim_step. }
    simpl. eapply prim_exec_cons_nofork. (* Comparison ["k" ≤ #0] *)
    { by prim_step. }
    rewrite /= bool_decide_false; [|lia].
    eapply prim_exec_cons_nofork.        (* If *)
    { by prim_step. }
    simpl. eapply prim_exec_cons_nofork. (* Decrementing "k" *)
    { by prim_step. }
                                         (* CAS *)
    simpl. eapply (prim_exec_cons_nofork _ _ _ (if: #true then _ else _)).
    { prim_step; [apply lookup_insert|by left]. }
    eapply prim_exec_cons_nofork.        (* If *)
    { by prim_step. }
    replace (Sn - 1) with (Z.of_nat n) by lia.
    rewrite insert_insert.
    apply prim_exec_nil.
  Qed.

  Lemma exec_tick_case_branch e1 v2 σ :
    prim_exec  (tick_case_branch (λ: <>, e1) v2)%E  σ ((tick e1) v2) σ  [].
  Proof.
    unfold tick_case_branch ; unlock.
    eapply prim_exec_cons_nofork.
    { by prim_step. }
    simpl. eapply prim_exec_cons_nofork.
    { by prim_step. }
    simpl. eapply prim_exec_cons_nofork.
    { by prim_step. }
    simpl. eapply prim_exec_cons_nofork.
    { by prim_step. }
    simpl. eapply prim_exec_cons_nofork.
    { by prim_step. }
    apply prim_exec_nil.
  Qed.

End Tick_exec.



(*
 * Simulation lemma
 *)

Section SimulationLemma.

  Context {Hloc : TickCounter}.

  Local Ltac exec_tick_success :=
    lazymatch goal with
    | |- prim_exec ?e _ _ _ _ =>
        reshape_expr false e ltac:(fun K e' =>
          eapply prim_exec_fill' with K e' _ ; [ done | done | ] ;
          eapply exec_tick_success
        )
    end ;
    done.
  (* in this tactic, the parameter ‘afterwards’ allows to unify the expression
   * resulting from the step before running the tactic ‘prim_step’;
   * this matters when the reduction rule to apply is directed by the syntax of
   * the result (more specifically, ‘CasFailS’ would be picked instead of
   * ‘CasSucS’ if we did not unify the result with ‘#true’ beforehand). *)
  Local Ltac tick_then_step_then afterwards :=
    eapply prim_exec_transitive_nofork ; first (
      exec_tick_success
    ) ;
    eapply prim_exec_cons_nofork, afterwards ; first (
      prim_step
    ).
  Local Ltac tick_then_step_then_stop :=
    tick_then_step_then prim_exec_nil.

  Lemma simulation_head_step_success n e1 σ1 κ e2 σ2 efs :
    σ2 !! ℓ = None →
    head_step e1 σ1 κ e2 σ2 efs →
    prim_exec «e1» S«σ1, S n» «e2» S«σ2, n» T«efs».
  Proof.
    intros Hℓ Hstep.
    destruct Hstep as
      [ (* RecS *) f x e σ
      | (* PairS *) v1 v2 σ
      | (* InjLS *) v σ
      | (* InjRS *) v σ
      | (* BetaS *) f x e1 v2 e' σ  ->
      | (* UnOpS *) op v v' σ  Hopeval
      | (* BinOpS *) op v1 v2 v' σ  Hopeval
      | (* IfTrueS  *) e1 e2 σ
      | (* IfFalseS *) e1 e2 σ
      | (* FstS *) v1 v2 σ
      | (* SndS *) v1 v2 σ
      | (* CaseLS *) v0 e1 e2 σ
      | (* CaseRS *) v0 e1 e2 σ
      | (* ForkS *) e σ
      | (* AllocS *) v σ l  Hfree_l
      | (* LoadS *) l v σ  Hbound_l
      | (* StoreS *) l v σ  Hisbound_l
      | (* CasFailS *) l v1 v2 vl σ  Hbound_l Hneq_vl_v1
      | (* CasSucS *) l v1 v2 σ  Hbound_l
      | (* FaaS *) l i1 i2 σ  Hbound_l
      ];
    simpl_trans;
    (try (
      assert (ℓ ≠ l) as I by (by apply lookup_insert_None in Hℓ as [ _ I ]) ;
      rewrite translationS_insert insert_commute ; last exact I
    )).
    (* RecS f x e σ : *)
    - eapply (prim_exec_cons _ _ _ _ _ [] _ _ []).
      + prim_step.
      + exec_tick_success.
    (* PairS *)
    - tick_then_step_then_stop.
    (* InjLS *)
    - tick_then_step_then_stop.
    (* InjRS *)
    - tick_then_step_then_stop.
    (* BetaS f x e1 v2 e' σ : *)
    - rewrite 2! translation_subst'.
      by tick_then_step_then_stop.
    (* UnOpS op v v' σ : *)
    - tick_then_step_then_stop.
      by apply un_op_eval_translation.
    (* BinOpS op v1 v2 v' σ : *)
    - tick_then_step_then_stop.
      by apply bin_op_eval_translation.
    (* IfTrueS e1 e2 σ : *)
    - tick_then_step_then_stop.
    (* IfFalseS e1 e2 σ : *)
    - tick_then_step_then_stop.
    (* FstS v1 v2 σ : *)
    - tick_then_step_then_stop.
    (* SndS v1 v2 σ : *)
    - tick_then_step_then_stop.
    (* CaseLS v0 e1 e2 σ : *)
    - tick_then_step_then exec_tick_case_branch.
    (* CaseRS v0 e1 e2 σ : *)
    - tick_then_step_then exec_tick_case_branch.
    (* ForkS e σ : *)
    - replace T« [e] » with ([« e »] ++ []) by apply app_nil_r.
      eapply prim_exec_cons.
      + prim_step.
      + exec_tick_success.
    (* AllocS v σ l : *)
    - tick_then_step_then_stop.
      apply lookup_insert_None ; auto using lookup_translationS_None.
    (* LoadS l v σ : *)
    - tick_then_step_then_stop.
      assert (ℓ ≠ l) as I by (intros <- ; rewrite -> Hℓ in * ; discriminate).
      rewrite lookup_insert_ne ; last exact I.
      by apply lookup_translationS_Some.
    (* StoreS l v σ : *)
    - tick_then_step_then_stop.
      rewrite lookup_insert_ne ; last exact I.
      by apply lookup_translationS_is_Some.
    (* CasFailS l v1 v2 vl σ : *)
    - tick_then_step_then_stop.
      + assert (ℓ ≠ l) as I by (intros <- ; rewrite -> Hℓ in * ; discriminate).
        rewrite lookup_insert_ne ; last done.
        by apply lookup_translationS_Some.
      + eauto using translationV_injective.
      + by apply vals_cas_compare_safe_translationV.
    (* CasSucS l v1 v2 σ : *)
    - tick_then_step_then_stop.
      + rewrite lookup_insert_ne ; last exact I.
        by apply lookup_translationS_Some.
      + by apply vals_cas_compare_safe_translationV.
    (* FaaS l i1 i2 σ : *)
    - tick_then_step_then_stop.
      rewrite lookup_insert_ne ; last exact I.
      change (#i1)%V with V« #i1 ».
      by apply lookup_translationS_Some.
  Qed.

  Lemma simulation_prim_step_success n e1 σ1 κ e2 σ2 efs :
    σ2 !! ℓ = None →
    prim_step e1 σ1 κ e2 σ2 efs →
    prim_exec «e1» S«σ1, S n» «e2» S«σ2, n» T«efs».
  Proof.
    intros Hℓ [ K e1' e2' -> -> H ].
    rewrite 2! translation_fill.
    by eapply prim_exec_fill, simulation_head_step_success.
  Qed.

  Lemma simulation_step_success n t1 σ1 κ t2 σ2 :
    σ2 !! ℓ = None →
    step (t1, σ1) κ (t2, σ2) →
    rtc erased_step (T«t1», S«σ1, S n») (T«t2», S«σ2, n»).
  Proof.
    intros Hℓ Hstep.
    destruct Hstep as [ e1 σ1_ e2 σ2_ efs t t' E1 E2 Hprimstep ] ;
    injection E1 as -> <- ;
    injection E2 as -> <-.
    repeat rewrite ? fmap_app ? fmap_cons.
    by eapply exec_frame_singleton_thread_pool, prim_exec_exec,
       simulation_prim_step_success.
  Qed.

  Lemma simulation_exec_success m n t1 σ1 t2 σ2 :
    σ2 !! ℓ = None →
    relations.nsteps erased_step m (t1, σ1) (t2, σ2) →
    rtc erased_step (T«t1», S«σ1, m+n») (T«t2», S«σ2, n»).
  Proof.
    make_eq (t1, σ1) as config1 E1.
    make_eq (t2, σ2) as config2 E2.
    intros Hℓ Hnsteps.
    revert t1 σ1 E1 ;
    induction Hnsteps as [ config | m' config1 (t3, σ3) config2 [κ Hstep] Hsteps IHnsteps ] ;
    intros t1 σ1 E1.
    - destruct E2 ; injection E1 as -> ->.
      apply rtc_refl.
    - destruct E2, E1.
      specialize (IHnsteps eq_refl t3 σ3 eq_refl).
      assert (σ3 !! ℓ = None) as Hℓ3 by (eapply loc_fresh_in_dom_nsteps ; cycle 1 ; eassumption).
      eapply rtc_transitive.
      + eapply simulation_step_success ; cycle -1 ; eassumption.
      + apply IHnsteps.
  Qed.

  Lemma simulation_exec_success' m n t1 σ1 t2 σ2 :
    σ2 !! ℓ = None →
    (m ≤ n)%nat →
    relations.nsteps erased_step m (t1, σ1) (t2, σ2) →
    rtc erased_step (T«t1», S«σ1, n») (T«t2», S«σ2, n-m»).
  Proof.
    intros Hℓ I.
    replace #n with #(m + (n-m))%nat ; last (repeat f_equal ; lia).
    by apply simulation_exec_success.
  Qed.

  (* from a reduction of the translated expression,
   * deduce a reduction of the source expression. *)

  (* note: this does not depend on the operational behavior of `tick`. *)

  Local Ltac exhibit_prim_step e2 :=
    eexists _, e2, _, _ ; simpl ; prim_step.

  Local Ltac eexhibit_prim_step :=
    eexists _, _, _, _ ; simpl ; prim_step.

  Lemma active_item_translation_reducible ki v σ m :
    ectx_item_is_active ki →
    loc_fresh_in_expr ℓ (fill_item ki v) →
    reducible (fill_item Ki«ki» V«v») S«σ, m» →
    reducible (fill_item ki v) σ.
  Proof.
    intros Hactive Hfresh (e2' & σ2' & efs &
                           [κ Hheadstep % active_item_prim_step_is_head_step]) ;
      last by apply is_active_translationKi.
    make_eq (fill_item Ki«ki» V«v») as e1' Ee1' ; rewrite Ee1' in Hheadstep.
    make_eq (S«σ, m») as σ1' Eσ1' ; rewrite Eσ1' in Hheadstep.
    destruct Hheadstep  as
      [ (* RecS *) f x e σ1
      | (* PairS *) v1 v2 σ1
      | (* InjLS *) v1 σ1
      | (* InjRS *) v1 σ1
      | (* BetaS *) f x e1 v2 e' σ1  ->
      | (* UnOpS *) op v1 v' σ1  Hopeval
      | (* BinOpS *) op v1 v2 v' σ1  Hopeval
      | (* IfTrueS  *) e1 e2 σ1
      | (* IfFalseS *) e1 e2 σ1
      | (* FstS *) v1 v2 σ1
      | (* SndS *) v1 v2 σ1
      | (* CaseLS *) v0 e1 e2 σ1
      | (* CaseRS *) v0 e1 e2 σ1
      | (* ForkS *) e σ1
      | (* AllocS *) v1 σ1 l  Hfree_l
      | (* LoadS *) l v1 σ1  Hbound_l
      | (* StoreS *) l v1 σ1  Hisbound_l
      | (* CasFailS *) l v1 v2 vl σ1  Hbound_l Hneq_vl_v1
      | (* CasSucS *) l v1 v2 σ1  Hbound_l
      | (* FaaS *) l i1 i2 σ1  Hbound_l
      ];
    destruct ki ; try contradiction Hactive ; try discriminate Ee1' ;
    injection Ee1' ; clear Ee1' ;
    repeat (intros -> || intros <- || intros -> % translationV_lit_inv || intros E) ;
    destruct Eσ1'.
    (* replacing the state S«σ, m» with S«σ»: *)
    all: first [
        apply lookup_insert_None in Hfree_l as [Hfree_l _]
      | apply lookup_insert_Some in Hbound_l as [ [<- _] | [_ Hbound_l] ] ; first naive_solver
      | apply lookup_insert_is_Some in Hisbound_l as [ <- | [_ Hisbound_l] ] ; first naive_solver
      | idtac
    ].
    (* PairS *)
    - eexhibit_prim_step.
    (* InjLS *)
    - eexhibit_prim_step.
    (* InjRS *)
    - eexhibit_prim_step.
    (* BetaS *)
    - destruct v ; try discriminate E.
      by eexhibit_prim_step.
    (* UnOpS *)
    - eexhibit_prim_step.
      by eapply un_op_eval_translation_inv.
    (* BinOpS *)
    - eexhibit_prim_step.
      by eapply bin_op_eval_translation_inv.
    (* IfTrueS *)
    - eexhibit_prim_step.
    (* IfFalseS *)
    - eexhibit_prim_step.
    (* FstS *)
    - destruct v ; try discriminate E.
      eexhibit_prim_step.
    (* SndS *)
    - destruct v ; try discriminate E.
      eexhibit_prim_step.
    (* CaseLS *)
    - destruct v ; try discriminate E.
      eexhibit_prim_step.
    (* CaseRS *)
    - destruct v ; try discriminate E.
      eexhibit_prim_step.
    (* AllocS *)
    - eexhibit_prim_step.
      by eapply lookup_translationS_None_inv.
    (* LoadS *)
    - apply lookup_translationS_Some_inv in Hbound_l as (? & ? & _).
      by eexhibit_prim_step.
    (* StoreS *)
    - eexhibit_prim_step.
      by eapply lookup_translationS_is_Some_inv.
    (* CasFailS *)
    - apply lookup_translationS_Some_inv in Hbound_l as (? & ? & ->).
      exhibit_prim_step (Val #false).
      + done.
      + intros ? % (f_equal translationV). contradiction.
      + by apply vals_cas_compare_safe_translationV_inv.
    (* CasSucS *)
    - apply lookup_translationS_Some_inv in Hbound_l as (? & ? & -> % translationV_injective).
      exhibit_prim_step (Val #true)%E.
      done. by apply vals_cas_compare_safe_translationV_inv.
    (* FaaS *)
    - apply lookup_translationS_Some_inv in Hbound_l as (? & ? & -> % eq_sym % translationV_lit_inv).
      by eexhibit_prim_step.
  Qed.

  (* assuming the safety of the translated expression,
   * a proof that the original expression is m-safe. *)

  Lemma safe_translation__nsafe_here m e σ :
    loc_fresh_in_expr ℓ e →
    (m > 0)%nat →
    safe «e» S«σ, m» →
    is_Some (to_val e) ∨ reducible e σ.
  Proof.
    intros Hfresh Im Hsafe.
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
                       (K & ki & v & -> & Hactive) ] ]].
      (* — either e = K[Var x]: *)
      + (* then [«fill K x»] is stuck: *)
        exfalso. clear -Hsafe. rewrite translation_fill in Hsafe.
        apply safe_fill_inv in Hsafe. destruct Hsafe as [_ Hsafe].
        destruct (Hsafe _ _ x eq_refl (rtc_refl _ _)) as
            [[? [=]]|(?&?&?&?&[K' ?? Hx ? Hred])]; first set_solver+; simpl in *.
        destruct (decide (K' = [])) as [->|(K''&Ki&->)%exists_last]; last first.
        { rewrite !fill_app in Hx. by destruct Ki. }
        simpl in Hx. subst e1'. inversion Hred.
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
         * (m ≥ 1 so ‘tick’ can be run): *)
        assert (
          prim_exec (fill_item Ki«ki» (tick V«v»)) S«σ, m»
                    (fill_item Ki«ki» V«v»)        S«σ, m-1» []
        ) as Hsteps % prim_exec_exec.
        {
          assert (fill [Ki«ki»] = fill_item Ki«ki») as E by reflexivity ; destruct E.
          apply prim_exec_fill. apply safe_fill_inv in Hsafe.
          rewrite {+1} (_ : m = S (m-1)) ; last lia.
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
  Lemma safe_translation__nsafe m n e σ t2 σ2 e2 :
    loc_fresh_in_expr ℓ e2 →
    σ2 !! ℓ = None →
    safe «e» S«σ, m» →
    relations.nsteps erased_step n ([e], σ) (t2, σ2) →
    (n < m)%nat →
    e2 ∈ t2 →
    is_Some (to_val e2) ∨ reducible e2 σ2.
  Proof.
    intros Hℓe Hℓσ Hsafe Hnsteps Inm He2.
    assert (safe «e2» S«σ2, m-n») as Hsafe2.
    {
      eapply safe_exec.
      - eapply elem_of_list_fmap_1. eassumption.
      - eassumption.
      - change [«e»] with T«[e]». apply simulation_exec_success' ; [ assumption | lia | assumption ].
    }
    assert (m - n > 0)%nat by lia.
    by eapply safe_translation__nsafe_here.
  Qed.

  (* assuming the adequacy of the translated expression,
   * a proof that the original expression has m-adequate results. *)

  (* FIXME : this is a weaker result than the adequacy result of Iris,
     where the predicate can also speak about the final state. *)
  Lemma adequate_translation__nadequate_result m n φ e σ t2 σ2 v2 :
    σ2 !! ℓ = None →
    adequate NotStuck «e» S«σ, m» (λ v σ, φ (invtranslationV v)) →
    relations.nsteps erased_step n ([e], σ) (Val v2 :: t2, σ2) →
    (n ≤ m)%nat →
    φ v2.
  Proof.
    intros Hfresh Hadq Hnsteps Inm.
    assert (safe «e» S«σ, m») as Hsafe by by eapply safe_adequate.
    replace (φ v2) with ((φ ∘ invtranslationV) (translationV v2))
      by (simpl ; by rewrite invtranslationV_translationV).
    eapply (adequate_result _ _ _ (λ v σ, φ (invtranslationV v))); first done.
    simpl. change [«e»%E] with T«[e]».
    replace (Val «v2» :: _) with (T«Val v2 :: t2») by done.
    eapply simulation_exec_success' ; eauto.
  Qed.

End SimulationLemma. (* we close the section here as we now want to quantify over all locations *)

(* now let’s combine the two results. *)

Lemma adequate_translation__nadequate m φ e σ :
  (∀ {Hloc : TickCounter}, adequate NotStuck «e» S«σ, m» (λ v σ, φ (invtranslationV v))) →
  nadequate NotStuck m e σ φ.
Proof.
  intros Hadq.
  split.
  (* (1) adequate result: *)
  - intros n t2 σ2 v2 Hnsteps Inm.
    (* build a location ℓ which is not in the domain of σ2: *)
    pose (Hloc := Build_TickCounter (fresh (dom (gset loc) σ2)) : TickCounter).
    assert (σ2 !! ℓ = None)
      by (simpl ; eapply (not_elem_of_dom (D:=gset loc)), is_fresh).
    by eapply adequate_translation__nadequate_result.
  (* (2) safety: *)
  - intros n t2 σ2 e2 _ Hnsteps Inm He2.
    (* build a location ℓ which is fresh in e2 and in the domain of σ2: *)
    pose (set1 := loc_set_of_expr e2 : gset loc).
    pose (set2 := dom (gset loc) σ2 : gset loc).
    pose (Hloc := Build_TickCounter (fresh (set1 ∪ set2)) : TickCounter).
    eassert (ℓ ∉ set1 ∪ set2) as [Hℓ1 Hℓ2] % not_elem_of_union
      by (unfold ℓ ; apply is_fresh).
    assert (loc_fresh_in_expr ℓ e2)
      by by apply loc_not_in_set_is_fresh_in_expr.
    assert (σ2 !! ℓ = None)
      by by (simpl ; eapply (not_elem_of_dom (D:=gset loc))).
    specialize (Hadq Hloc) as Hsafe % safe_adequate.
    by eapply safe_translation__nsafe.
Qed.

End Simulation.

