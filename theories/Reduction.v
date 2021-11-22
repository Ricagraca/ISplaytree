From iris_time Require Import Base.
From stdpp Require Import fin_maps gmap.
(* FIXME: for obscure reasons, lang must appear after adequacy on this line: *)
From iris_time.heap_lang Require Import notation adequacy lang.
From iris_time Require Import Tactics.

Implicit Type e : expr.
Implicit Type v : val.
Implicit Type σ : state.
Implicit Type t : list expr.
Implicit Type K : ectx heap_ectx_lang.
Implicit Type m n : nat.



(*
 * Reduction
 *)

Section Reduction.

  Definition bounded_time e σ m : Prop :=
    ∀ t2 σ2 n, relations.nsteps erased_step n ([e], σ) (t2, σ2) → (n ≤ m)%nat.

  Inductive prim_exec (e1 : expr) (σ1 : state) : expr → state → list expr → Prop :=
  | prim_exec_nil :
      prim_exec e1 σ1 e1 σ1 []
  | prim_exec_cons (κ : list Empty_set)
                   (e2 : expr) (σ2 : state) (efs2 : list expr) e3 σ3 efs3 :
      prim_step e1 σ1 κ e2 σ2 efs2 →
      prim_exec e2 σ2 e3 σ3 efs3 →
      prim_exec e1 σ1 e3 σ3 (efs2 ++ efs3).

  Lemma prim_exec_cons_nofork e1 σ1 κ e2 σ2 e3 σ3 efs3 :
    prim_step e1 σ1 κ e2 σ2 []   →
    prim_exec e2 σ2 e3 σ3 efs3 →
    prim_exec e1 σ1 e3 σ3 efs3.
  Proof.
    intros. change efs3 with ([] ++ efs3). by eapply prim_exec_cons.
  Qed.

  Lemma prim_exec_transitive e1 σ1 e2 σ2 efs2 e3 σ3 efs3 :
    prim_exec e1 σ1 e2 σ2 efs2 →
    prim_exec e2 σ2 e3 σ3 efs3 →
    prim_exec e1 σ1 e3 σ3 (efs2 ++ efs3).
  Proof.
    induction 1 ; intros ? ; first assumption.
    rewrite - app_assoc. eapply prim_exec_cons ; eauto.
  Qed.
  Lemma prim_exec_transitive_nofork e1 σ1 e2 σ2 e3 σ3 efs3 :
    prim_exec e1 σ1 e2 σ2 [] →
    prim_exec e2 σ2 e3 σ3 efs3 →
    prim_exec e1 σ1 e3 σ3 efs3.
  Proof.
    intros. change efs3 with ([] ++ efs3). by eapply prim_exec_transitive.
  Qed.

  Lemma thread_pool_grows_after_step t1 σ1 κ t2 σ2 :
    step (t1, σ1) κ (t2, σ2) →
    (length t1 ≤ length t2)%nat.
  Proof.
    intros [e1 σ1_ e2 σ2_ efs t t' E1 E2 Hstep] ;
    injection E1 as -> <- ; injection E2 as -> <-.
    repeat rewrite ? app_length ? cons_length. lia.
  Qed.
  Lemma thread_pool_grows_after_exec t1 σ1 t2 σ2 :
    rtc erased_step (t1, σ1) (t2, σ2) →
    (length t1 ≤ length t2)%nat.
  Proof.
    make_eq (t1, σ1) as config1 E1.
    make_eq (t2, σ2) as config2 E2.
    intros Hsteps.
    revert t1 σ1 E1 ;
    induction Hsteps as [ config | config1 (t3, σ3) config2 [κ Hstep] _ IHsteps ] ;
    intros t1 σ1 E1.
    - destruct E2 ; injection E1 as -> ->.
      done.
    - destruct E2, E1.
      eapply Nat.le_trans.
      + by eapply thread_pool_grows_after_step.
      + by eapply IHsteps.
  Qed.
  Lemma thread_pool_is_cons_after_step t1 σ1 κ t2 σ2 :
    step (t1, σ1) κ (t2, σ2) →
    ∃ e2 t2', t2 = e2 :: t2'.
  Proof.
    intros Hstep.
    assert (0 < length t1)%nat as I.
    {
      destruct Hstep as [e1 σ1_ _ _ _ ta tb E1 _ _] ; injection E1 as -> _.
      rewrite app_length cons_length. lia.
    }
    destruct t2.
    - apply thread_pool_grows_after_step, le_not_lt in Hstep. contradiction.
    - eauto.
  Qed.
  Lemma thread_pool_is_cons_after_exec e1 t1' σ1 t2 σ2 :
    rtc erased_step (e1 :: t1', σ1) (t2, σ2) →
    ∃ e2 t2', t2 = e2 :: t2'.
  Proof.
    destruct t2.
    - intros ? % thread_pool_grows_after_exec % Nat.nle_succ_0 ; contradiction.
    - eauto.
  Qed.

  Lemma step_insert_in_thread_pool (n : nat) t t1 σ1 κ t2 σ2 :
    (n ≤ length t1)%nat →
    step (t1, σ1) κ (t2, σ2) →
    step (take n t1 ++ t ++ drop n t1, σ1) κ (take n t2 ++ t ++ drop n t2, σ2).
  Proof.
    intros I Hstep.
    destruct Hstep as [e1 σ1_ e2 σ2_ efs ta tb E1 E2 Hprimstep] ; simpl in * ;
    injection E1 as -> <- ; injection E2 as -> <-.
    pose proof (le_lt_dec n (length ta)) as J.
    destruct J as [ J | J ].
    (* if n ≤ length ta: *)
    - rewrite ! take_app_le ? drop_app_le ; [ | exact J ..].
      rewrite ! app_assoc.
      eapply step_atomic ; last eassumption ; reflexivity.
    (* if length ta < n: *)
    - rewrite app_length cons_length in I.
      assert (  (length ta ≤ n)%nat
              ∧ (0 < n - length ta)%nat
              ∧ (n - length ta - 1 ≤ length tb)%nat )
        as (J1 & J2 & J3) by lia.
      rewrite ! take_app_ge ? drop_app_ge ; [ | exact J1 ..].
      rewrite ! take_cons   ? drop_cons   ; [ | exact J2 ..].
      rewrite   take_app_le ? drop_app_le ; [ | exact J3 ..].
      eapply step_atomic ; last eassumption ; rewrite - ! app_assoc /= //.
  Qed.
  Lemma exec_insert_in_thread_pool (n : nat) t t1 σ1 t2 σ2 :
    (n ≤ length t1)%nat →
    rtc erased_step (t1, σ1) (t2, σ2) →
    rtc erased_step (take n t1 ++ t ++ drop n t1, σ1) (take n t2 ++ t ++ drop n t2, σ2).
  Proof.
    make_eq (t1, σ1) as config1 E1.
    make_eq (t2, σ2) as config2 E2.
    intros I H.
    revert t1 σ1 E1 I ;
    induction H as [ config | config1 (t3, σ3) config2 [κ Hstep] _ IHsteps ] ;
    intros t1 σ1 E1 I.
    - destruct E2 ; injection E1 as -> ->.
      apply rtc_refl.
    - destruct E2, E1.
      eapply rtc_l.
      + exists κ. by eapply step_insert_in_thread_pool.
      + by eapply IHsteps, le_trans, thread_pool_grows_after_step.
  Qed.
  Lemma exec_frame_thread_pool t1 σ1 t2 σ2 ta tb :
    rtc erased_step (t1, σ1) (t2, σ2) →
    let n := length t1 in
    rtc erased_step (ta ++ t1 ++ tb, σ1) (ta ++ take n t2 ++ tb ++ drop n t2, σ2).
  Proof.
    intros Hsteps n.
    replace (t1 ++ tb) with (take n t1 ++ tb ++ drop n t1)
      by by rewrite firstn_all drop_all app_nil_r.
    apply (exec_insert_in_thread_pool 0 ta), (exec_insert_in_thread_pool n tb) ; first lia ; done.
  Qed.
  Lemma exec_frame_singleton_thread_pool e1 σ1 e2 t2 σ2 t t' :
    rtc erased_step ([e1], σ1) (e2 :: t2, σ2) →
    rtc erased_step (t ++ e1 :: t', σ1) (t ++ e2 :: t' ++ t2, σ2).
  Proof.
    change (e1 :: t') with ([e1] ++ t').
    apply exec_frame_thread_pool.
  Qed.

  Lemma prim_step_step e1 σ1 κ e2 σ2 efs :
    prim_step e1 σ1 κ e2 σ2 efs →
    step ([e1], σ1) κ (e2 :: efs, σ2).
  Proof.
    intros. by eapply step_atomic with _ _ _ _ _ [] [].
  Qed.
  Lemma prim_exec_exec e1 σ1 e2 σ2 efs :
    prim_exec e1 σ1 e2 σ2 efs →
    rtc erased_step ([e1], σ1) (e2 :: efs, σ2).
  Proof.
    unfold erased_step.
    induction 1 ; econstructor ; eauto using prim_step_step, (exec_frame_singleton_thread_pool _ _ _ _ _ []).
  Qed.

  Lemma prim_step_fill K e1 σ1 κ e2 σ2 efs :
    prim_step e1 σ1 κ e2 σ2 efs →
    prim_step (fill K e1) σ1 κ (fill K e2) σ2 efs.
  Proof.
    intros [ K' e1' e2' -> -> Hheadstep ].
    rewrite - 2! fill_app.
    by econstructor.
  Qed.
  Lemma prim_exec_fill K e1 σ1 e2 σ2 efs :
    prim_exec e1 σ1 e2 σ2 efs →
    prim_exec (fill K e1) σ1 (fill K e2) σ2 efs.
  Proof.
    induction 1 ; econstructor ; eauto using prim_step_fill.
  Qed.
  Lemma prim_exec_fill' K e1 σ1 e2 σ2 efs e1' e2' :
    fill K e1 = e1' →
    fill K e2 = e2' →
    prim_exec e1 σ1 e2 σ2 efs →
    prim_exec e1' σ1 e2' σ2 efs.
  Proof.
    intros <- <-. apply prim_exec_fill.
  Qed.

  Lemma step_fill K e1 t1' σ1 κ e2 t2' σ2 :
    step (e1 :: t1', σ1) κ (e2 :: t2', σ2) →
    step (fill K e1 :: t1', σ1) κ (fill K e2 :: t2', σ2).
  Proof.
    intros Hstep.
    destruct Hstep as [ e1' ? e2' ? efs ta tb E1 E2 ] ;
    destruct ta as [ | ? ta ] ;
    injection E1 as <- -> <- ; injection E2 as <- -> <-.
    - by eapply step_atomic with _ _ _ _ _ [] _, prim_step_fill.
    - by eapply step_atomic with _ _ _ _ _ (fill K e2 :: ta) tb.
  Qed.
  Lemma exec_fill K e1 t1' σ1 e2 t2' σ2 :
    rtc erased_step (e1 :: t1', σ1) (e2 :: t2', σ2) →
    rtc erased_step (fill K e1 :: t1', σ1) (fill K e2 :: t2', σ2).
  Proof.
    make_eq (e1 :: t1', σ1) as config1 E1.
    make_eq (e2 :: t2', σ2) as config2 E2.
    intros Hsteps.
    revert e1 t1' σ1 E1 ;
    induction Hsteps as [ config | config1 (t3, σ3) config2 [κ Hstep] _ IHsteps ] ;
    intros e1 t1' σ1 E1.
    - destruct E2 ; injection E1 as -> -> ->.
      apply rtc_refl.
    - destruct E2, E1.
      assert (∃ e3 t3', t3 = e3 :: t3') as (e3 & t3' & ->)
        by by eapply thread_pool_is_cons_after_step.
      eapply rtc_l.
      + exists κ. by apply step_fill.
      + by apply IHsteps.
  Qed.

  Lemma reducible_fill K e σ :
    reducible e σ →
    reducible (fill K e) σ.
  Proof.
    intros (κ & e' & σ' & efs & Hstep).
    eexists _, _, _, _.
    by apply prim_step_fill.
  Qed.

End Reduction.

(*
 * Fresh locations
 *)

Section FreshLocation.

  Lemma loc_fresh_in_dom_head_step ℓ e1 σ1 κ e2 σ2 efs :
    σ2 !! ℓ = None →
    head_step e1 σ1 κ e2 σ2 efs →
    σ1 !! ℓ = None.
  Proof.
    intros Hℓ H ; destruct H ; try done ;
    by apply lookup_insert_None in Hℓ as [ Hℓ _ ].
  Qed.
  Lemma loc_fresh_in_dom_prim_step ℓ e1 σ1 κ e2 σ2 efs :
    σ2 !! ℓ = None →
    prim_step e1 σ1 κ e2 σ2 efs →
    σ1 !! ℓ = None.
  Proof.
    intros Hℓ H ; destruct H ;
    by eapply loc_fresh_in_dom_head_step.
  Qed.
  Lemma loc_fresh_in_dom_step ℓ t1 σ1 κ t2 σ2 :
    σ2 !! ℓ = None →
    step (t1, σ1) κ (t2, σ2) →
    σ1 !! ℓ = None.
  Proof.
    intros Hℓ H ; destruct H as [ ? ? ? ? ? ? ? E1 E2 Hstep ] ;
    injection E1 as -> <- ; injection E2 as -> <- ;
    by eapply loc_fresh_in_dom_prim_step.
  Qed.
  Lemma loc_fresh_in_dom_nsteps ℓ m t1 σ1 t2 σ2 :
    σ2 !! ℓ = None →
    relations.nsteps erased_step m (t1, σ1) (t2, σ2) →
    σ1 !! ℓ = None.
  Proof.
    make_eq (t1, σ1) as config1 E1.
    make_eq (t2, σ2) as config2 E2.
    intros Hℓ H.
    revert t1 σ1 E1 ;
    induction H as [ config | ? config1 (t3, σ3) config2 [κ Hstep] _ IHnsteps ] ;
    intros t1 σ1 E1.
    - destruct E2 ; injection E1 as -> ->.
      done.
    - destruct E2, E1.
      specialize (IHnsteps eq_refl t3 σ3 eq_refl).
      eapply loc_fresh_in_dom_step; eassumption.
  Qed.

  Fixpoint loc_set_of_expr e : gset loc :=
    match e with
    | Val v => loc_set_of_val v
    | Var _ => empty
    | Rec _ _ e
    | UnOp _ e | Fst e | Snd e | InjL e | InjR e | Fork e | Alloc e | Load e =>
       loc_set_of_expr e
    | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 | Store e1 e2 | FAA e1 e2 =>
       loc_set_of_expr e1 ∪ loc_set_of_expr e2
    | If e0 e1 e2 | Case e0 e1 e2 | CAS e0 e1 e2 =>
       loc_set_of_expr e0 ∪ loc_set_of_expr e1 ∪ loc_set_of_expr e2
    end
  with loc_set_of_val v : gset loc :=
    match v with
    | LitV (LitLoc l) => {[ l ]}
    | LitV _ => empty
    | RecV _ _ e => loc_set_of_expr e
    | InjLV v | InjRV v => loc_set_of_val v
    | PairV v1 v2 => loc_set_of_val v1 ∪ loc_set_of_val v2
    end.

  Fixpoint loc_fresh_in_expr (ℓ : loc) e : bool :=
    match e with
    | Val v => loc_fresh_in_val (ℓ : loc) v
    | Var _ => true
    | Rec _ _ e
    | UnOp _ e | Fst e | Snd e | InjL e | InjR e | Fork e | Alloc e | Load e =>
       loc_fresh_in_expr ℓ e
    | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 | Store e1 e2 | FAA e1 e2 =>
       loc_fresh_in_expr ℓ e1 && loc_fresh_in_expr ℓ e2
    | If e0 e1 e2 | Case e0 e1 e2 | CAS e0 e1 e2 =>
       loc_fresh_in_expr ℓ e0 && loc_fresh_in_expr ℓ e1 && loc_fresh_in_expr ℓ e2
    end
  with loc_fresh_in_val (ℓ : loc) v : bool :=
    match v with
    | LitV (LitLoc l) => bool_decide (ℓ ≠ l)
    | LitV _ => true
    | RecV _ _ e => loc_fresh_in_expr ℓ e
    | InjLV v | InjRV v => loc_fresh_in_val ℓ v
    | PairV v1 v2 => loc_fresh_in_val ℓ v1 && loc_fresh_in_val ℓ v2
    end.

  Lemma loc_not_in_set_is_fresh_in_expr (ℓ : loc) e :
    ℓ ∉ loc_set_of_expr e →
    loc_fresh_in_expr ℓ e
  with loc_not_in_set_is_fresh_in_val (ℓ : loc) v :
    ℓ ∉ loc_set_of_val v →
    loc_fresh_in_val ℓ v.
  Proof.
    - destruct e; simpl; intros Hnotin ;
        repeat (apply not_elem_of_union in Hnotin as [Hnotin ?]) ;
        auto 10.
    - destruct v as [[]| | | |]; simpl; intros Hnotin ;
        repeat (apply not_elem_of_union in Hnotin as [Hnotin ?]) ;
        auto 10.
      (* only remaining case: v = LitV l *)
      apply bool_decide_pack. set_solver.
  Qed.

  Lemma loc_fresh_in_expr_fill_inv (ℓ : loc) K e :
    loc_fresh_in_expr ℓ (fill K e) →
    loc_fresh_in_expr ℓ e.
  Proof.
    revert e.
    induction K as [ | Ki K IH ] ; first done.
    intros e Hitem % IH.
    destruct Ki ; naive_solver.
  Qed.

End FreshLocation.



(*
 * Active context items and maximal contexts
 *)

Section ActiveItem.

  Definition ectx_item_is_active (Ki : ectx_item) : bool :=
    match Ki with
    | AppLCtx _ | UnOpCtx _ | BinOpLCtx _ _ | IfCtx _ _
    | PairLCtx _ | FstCtx | SndCtx | InjLCtx | InjRCtx
    | CaseCtx _ _ | AllocCtx | LoadCtx | StoreLCtx _ | CasLCtx _ _ | FaaLCtx _ => true
    | _ => false
    end.

  Definition immediate_sub_redexes_are_values e0 : Prop :=
    ∀ ki e1, e0 = fill_item ki e1 → is_Some (to_val e1).

  Definition maximal_ectx e K0 e0 : Prop :=
    e = fill K0 e0
  ∧ to_val e0 = None
  ∧ immediate_sub_redexes_are_values e0.

  Local Ltac maximal_ectx_from_subterm IH :=
    let E := fresh "E" in
    let v1 := fresh "v1" in
    lazymatch type of IH with to_val ?e1 = None → _ =>
      destruct (to_val e1) as [ v1 | ] eqn:E ; [
        apply of_to_val in E as <-
      |
        let K0 := fresh "K0" in
        destruct (IH eq_refl) as (K0 & ? & -> & ? & ?) ; clear IH ;
        lazymatch goal with |- to_val ?e = None → _ =>
          reshape_expr false e ltac:(fun K1 _ =>
            eexists (K0 ++ K1), _ ; split ; [|split] ;
            [ by erewrite fill_app | assumption | assumption ]
          )
        end
      ] ; []
    end.

  Local Ltac maximal_ectx_empty :=
    eexists [], _ ; split ; [|split] ;
    [ reflexivity | assumption | ] ;
    intros [] ; inversion 1 ; eauto.

  Lemma not_val_maximal_ectx e :
    to_val e = None →
    ∃ K0 e0, maximal_ectx e K0 e0.
  Proof.
    induction e ;
      try maximal_ectx_from_subterm IHe  ;
      try maximal_ectx_from_subterm IHe3 ;
      try maximal_ectx_from_subterm IHe2 ;
      try maximal_ectx_from_subterm IHe1 ;
      maximal_ectx_empty.
  Qed.

  Local Ltac rewrite_immediate_sub_redexes_into_values Hsubterms :=
    (* we perform rewriting for each immediate sub-redex of e (we read e again
     * after each iteration because previous rewritings reveal new contexts): *)
    repeat (lazymatch type of Hsubterms with immediate_sub_redexes_are_values ?e =>
        reshape_expr false e ltac:(fun K e1 =>
          (* we are only interested in contexts of depth 1; moreover, for
           * termination purposes, we do nothing when the hole e1 is already
           * a value: *)
          lazymatch constr:(pair K e1) with
          | pair _ (Val ?v) =>
              fail
          | pair [ ?Ki ] _ =>
              let v := fresh "v" in
              destruct (Hsubterms Ki e1 eq_refl) as (v & <-%of_to_val)
          end
        )
    end).

  Local Ltac exhibit_active_item :=
    lazymatch goal with |- exists ki v, ?e = fill_item ki (Val v) ∧ Is_true (ectx_item_is_active ki) =>
        reshape_expr false e ltac:(fun K e1 =>
          (* we are only interested in contexts of depth 1; moreover, we are
           * supposed to get a value in the hole: *)
          lazymatch constr:(pair K e1) with
          | pair [ ?Ki ] (Val ?v) =>
              (* we try to conclude with that context item (if it is not active,
               * then the proof will fail, thus we do not need to test it ourself): *)
              by exists Ki, v
          end
        )
    end.

  Lemma sub_redexes_values_active_item e0 :
    to_val e0 = None →
    immediate_sub_redexes_are_values e0 →
      (∃ x, e0 = Var x)
    ∨ (∃ e1, e0 = Fork e1)
    ∨ (∃ f x e1, e0 = Rec f x e1)
    ∨ (∃ (ki : ectx_item) (v : val),
        e0 = fill_item ki v
      ∧ ectx_item_is_active ki).
  Proof.
    intros Hnotval Hsubterms.
    destruct e0 ;
      rewrite_immediate_sub_redexes_into_values Hsubterms ;
      (* most cases are solved by exhibiting a solution: *)
      try (right ; right; right; exhibit_active_item) ;
      (* some cases contradict the assumption that e0 is not a value: *)
      try discriminate Hnotval.
    (* remaining cases : *)
    (* Var *)
    - eauto.
    (* Rec *)
    - eauto 10.
    (* Fork *)
    - eauto 10.
  Qed.

  Lemma not_val_fill_active_item e :
    to_val e = None →
      (∃ K x, e = fill K (Var x))
    ∨ (∃ K e1, e = fill K (Fork e1))
    ∨ (∃ K f x e1, e = fill K (Rec f x e1))
    ∨ (∃ K ki v, e = fill K (fill_item ki v) ∧ ectx_item_is_active ki).
  Proof.
    intros (K & e0 & -> & Hnotval & Hsubterms) % not_val_maximal_ectx.
    apply sub_redexes_values_active_item in Hsubterms
      as [ [x ->] | [[e1 ->] | [(f & x & e1 & ->) | (ki & v & -> & Hactive)]] ];
    naive_solver.
  Qed.

  Lemma active_item_not_val ki e :
    ectx_item_is_active ki →
    to_val (fill_item ki e) = None.
  Proof.
    destruct ki ; try contradiction ; auto.
  Qed.

  Lemma active_item_sub_redexes_values ki v :
    ectx_item_is_active ki →
    immediate_sub_redexes_are_values (fill_item ki v).
  Proof.
    destruct ki ; try contradiction ; intros _ ;
    intros [] ? ; try discriminate 1 ;
    injection 1 ; repeat (intros <- || intros _) ; eauto.
  Qed.

  Lemma active_item_prim_step_is_head_step ki v σ1 κ e2 σ2 efs :
    ectx_item_is_active ki →
    prim_step (fill_item ki v) σ1 κ e2 σ2 efs →
    head_step (fill_item ki v) σ1 κ e2 σ2 efs.
  Proof.
    intros Hactive Hstep.
    destruct Hstep as [K' e1' e2' E1 E2 Hheadstep] ; simpl in *.
    pose revK' := rev K' ; replace K' with (rev revK') in * by apply rev_involutive ; clearbody revK'.
    destruct revK' as [ | ki' revK' ].
    - by rewrite E1 E2.
    - exfalso.
      rewrite /= fill_app /= in E1.
      assert (immediate_sub_redexes_are_values (fill_item ki v)) as Hsubterms
        by by apply active_item_sub_redexes_values.
      assert (is_Some $ to_val (fill (rev revK') e1'))
        by by eapply Hsubterms.
      eapply val_head_stuck, fill_not_val, eq_None_not_Some in Hheadstep.
      eauto.
  Qed.

End ActiveItem.



(*
 * Safety
 *)

Section Safety.

  Definition safe e σ : Prop :=
    adequate NotStuck e σ (λ _ _, True).

(*
  Lemma safe_alt e σ :
    safe e σ
    ↔
    ∀ t2 σ2 e2,
      rtc step ([e], σ) (t2, σ2) →
      e2 ∈ t2 →
      is_Some (to_val e2) ∨ reducible e2 σ2.
  Proof.
    split.
    - intros [ _ H ]. eauto.
    - intros H. split ; eauto.
  Qed.
*)

  Lemma safe_adequate e σ (φ : val → state → Prop) :
    adequate NotStuck e σ φ →
    safe e σ.
  Proof.
    intros [_ ?]. by split.
  Qed.

(*
  Lemma safe_iff_adequate e σ :
    safe e σ
    ↔
    ∃ (φ : val → Prop), adequate NotStuck e σ φ.
  Proof.
    split.
    - eauto.
    - intros [_ [_ ?]]. by split.
  Qed.

  Lemma not_safe_iff_not_adequate e σ :
    ¬ safe e σ
    ↔
    ∀ (φ : val → Prop), ¬ adequate NotStuck e σ φ.
  Proof.
    split.
    - intros Hnotsafe _ Hsafe%safe_adequate. contradiction.
    - intros Hnotadq [φ Hadq]%safe_iff_adequate. eapply Hnotadq, Hadq.
  Qed.
*)

  Lemma safe_here e σ :
    safe e σ →
    is_Some (to_val e) ∨ reducible e σ.
  Proof.
    intros H. apply H with [e] ; constructor.
  Qed.

  Lemma safe_exec e1 σ1 t2 e2 σ2 :
    e2 ∈ t2 →
    safe e1 σ1 →
    rtc erased_step ([e1], σ1) (t2, σ2) →
    safe e2 σ2.
  Proof.
    intros E2 Hsafe1 Hsteps1to2.
    split ; first done. intros t3 σ3 e3 _ Hsteps2to3 E3.
    apply elem_of_list_split in E2 as (t2' & t2'' & ->).
    apply thread_pool_is_cons_after_exec in Hsteps2to3 as E3' ; destruct E3' as (e3' & t3' & ->).
    assert (e3 ∈ t2' ++ e3' :: t2'' ++ t3') by set_solver.
    eapply Hsafe1 ; try done.
    eapply rtc_transitive ; first eassumption.
    eapply exec_frame_singleton_thread_pool ; eassumption.
  Qed.

  Lemma not_safe_exec e1 σ1 t2 e2 σ2 :
    e2 ∈ t2 →
    ¬ safe e2 σ2 →
    rtc erased_step ([e1], σ1) (t2, σ2) →
    ¬ safe e1 σ1.
  Proof.
    eauto 10 using safe_exec.
  Qed.

  Lemma safe_exec_nofork e1 σ1 e2 σ2 :
    safe e1 σ1 →
    rtc erased_step ([e1], σ1) ([e2], σ2) →
    safe e2 σ2.
  Proof.
    intros. eapply safe_exec ; [ constructor | eassumption | eassumption ].
  Qed.

  Lemma safe_prim_step e1 σ1 κ e2 σ2 efs :
    safe e1 σ1 →
    prim_step e1 σ1 κ e2 σ2 efs →
    safe e2 σ2.
  Proof.
    intros. eapply safe_exec ; [ constructor | eassumption | ].
    eapply rtc_l, rtc_refl. exists κ. apply prim_step_step. eassumption.
  Qed.

  Lemma not_safe_prim_step e1 σ1 κ e2 σ2 efs :
    ¬ safe e2 σ2 →
    prim_step e1 σ1 κ e2 σ2 efs →
    ¬ safe e1 σ1.
  Proof.
    eauto using safe_prim_step.
  Qed.

  Lemma stuck_not_safe e1 σ1 :
    stuck e1 σ1 →
    ¬ safe e1 σ1.
  Proof.
    intros Hstuck Hsafe%safe_here.
    destruct Hstuck as [ Hnotval%eq_None_not_Some Hnotred%not_reducible ].
    destruct Hsafe as [ Hval | Hred ] ; contradiction.
  Qed.

  Lemma stuck_fill K e σ :
    stuck e σ →
    stuck (fill K e) σ.
  Proof.
    intros [ Hnotval Hirred ].
    unfold stuck.
    split.
    - by apply fill_not_val.
    - intros e' σ' efs κ [K1 e1 e'1 E -> Hstep] ; simpl in *.
      eapply step_by_val in E as HK ; try done ; destruct HK as [K'1 -> ].
      rewrite fill_app in E ; apply fill_inj in E.
      eapply Hirred. econstructor ; [|reflexivity|] ; eassumption.
  Qed.

  Lemma safe_fill_inv K e σ :
    safe (fill K e) σ →
    safe e σ.
  Proof.
    intros [_ Hsafe]. split ; first done.
    intros t' σ' e' _ Hsteps He'.
    destruct He' as [ e' t' | e' e'0 t' He' ].
    - eapply exec_fill in Hsteps.
      specialize (Hsafe _ _ _ eq_refl Hsteps (elem_of_list_here _ _)). clear Hsteps.
      destruct Hsafe as [ Hval | Hred ].
      + left. by eapply fill_val.
      + destruct (to_val e') eqn:Hnotval; [by left; eauto|]. right.
        destruct Hred as (κ & _ & σ'' & efs & [ K2 e'2 e''2 Efill _ Hstep ]) ; simpl in *.
        eapply step_by_val in Efill as Efill' ; try eassumption ; destruct Efill' as [K' ->].
        rewrite fill_app in Efill ; apply fill_inj in Efill as ->.
        exists κ, (fill K' e''2), σ'', efs.
        by apply Ectx_step'.
    - eapply exec_fill in Hsteps.
      eapply Hsafe ; eauto using elem_of_list_further.
  Qed.

  Lemma not_safe_fill K e σ :
    ¬ safe e σ →
    ¬ safe (fill K e) σ.
  Proof.
    eauto using safe_fill_inv.
  Qed.

  Lemma not_safe_fill' K e e' σ :
    fill K e = e' →
    ¬ safe e σ →
    ¬ safe e' σ.
  Proof.
    intros <-. apply not_safe_fill.
  Qed.

  (* n-adequacy: *)
  Record nadequate (s : stuckness) (n : nat) e1 σ1 (φ : val → Prop) : Prop := {
    nadequate_result k t2 σ2 v2 :
     relations.nsteps erased_step k ([e1], σ1) (Val v2 :: t2, σ2) → (k ≤ n)%nat → φ v2;
    nadequate_not_stuck k t2 σ2 e2 :
     s = NotStuck →
     relations.nsteps erased_step k ([e1], σ1) (t2, σ2) →
     (k < n)%nat →
     e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2)
  }.

  (* n-safety: *)
  Definition nsafe n e σ : Prop :=
    nadequate NotStuck n e σ (λ _, True).

End Safety.
