From stdpp Require Import fin_maps.
From iris_time.heap_lang Require Export notation proofmode.
From iris_time Require Import Reduction.

Implicit Type e : expr.
Implicit Type v : val.
Implicit Type σ : state.
Implicit Type t : list expr.
Implicit Type K : ectx heap_ectx_lang.
Implicit Type m n : nat.



(*
 * Translation with any arbitrary expression for [tick]
 *)

(* “tick” is a typeclass so that it can be made an implicit argument of the
 * translation and be inferred automatically from the context.
   This also make it possible to share notations. *)
Class Tick := tick : val.

Section Translation.

  Context {Htick : Tick}.

  (* Unfortunately, the operational semantics of [match] in our language is
   * ad-hoc somehow, as the rule is:
   *     Case (InjL v) e1 e2  →  e1 v
   * Instead of the more canonical rule:
   *     Case (InjL v) (x1. e1) (x2. e2)  →  e1 [x1 := v]
   * This means that the reduction of a match construct really takes two steps,
   * since we still have to reduce the application; hence, in our time credit
   * model, a match construct will cost two credits.
   * It also means that the “branch” [e1] is not constrained be a λ-abstraction,
   * and can reduce after the reduction of the [match] but before it is applied
   * to [v]!
   * This ad-hoc semantics calls for an ad-hoc definition of the translation in
   * that case because, to observe the simulation lemma, the translation of
   * [Case (InjL v) e1 e2] must reduce to the translation of [e1 v], which is
   * [(tick «e1») «v»]. To do so --which means preserving the weird evaluation
   * order--, we use the helper term below: *)
  Definition tick_case_branch : val :=
    (λ: "f" "x", tick ("f" #()) "x")%V.

  Fixpoint translation (e : expr) : expr :=
    match e with
    (* Base lambda calculus *)
    | Var _           => e
    | Rec f x e       => tick $ Rec f x (translation e)
    | App e1 e2       => (tick $ translation e1) (translation e2)
    | Val v           => Val $ translationV v
    (* Base types and their operations *)
    | UnOp op e       => UnOp op (tick $ translation e)
    | BinOp op e1 e2  => BinOp op (tick $ translation e1) (translation e2)
    | If e0 e1 e2     => If (tick $ translation e0) (translation e1) (translation e2)
    (* Products *)
    | Pair e1 e2      => Pair (tick $ translation e1) (translation e2)
    | Fst e           => Fst (tick $ translation e)
    | Snd e           => Snd (tick $ translation e)
    (* Sums *)
    | InjL e          => InjL (tick $ translation e)
    | InjR e          => InjR (tick $ translation e)
    | Case e0 e1 e2   =>
        Case (tick $ translation e0)
          (tick_case_branch (λ: <>, translation e1))
          (tick_case_branch (λ: <>, translation e2))
    (* Concurrency *)
    | Fork e          => tick $ Fork (translation e)
    (* Heap *)
    | Alloc e         => Alloc (tick $ translation e)
    | Load e          => Load (tick $ translation e)
    | Store e1 e2     => Store (tick $ translation e1) (translation e2)
    | CAS e0 e1 e2    => CAS (tick $ translation e0) (translation e1) (translation e2)
    | FAA e1 e2       => FAA (tick $ translation e1) (translation e2)
    end %E
  with translationV (v : val) : val :=
    match v with
    | RecV f x e    => RecV f x (translation e)
    | LitV _        => v
    | PairV v1 v2   => PairV (translationV v1) (translationV v2)
    | InjLV v       => InjLV (translationV v)
    | InjRV v       => InjRV (translationV v)
    end.

  Definition translationS (σ : state) : state :=
    translationV <$> σ.

  Let tickCtx : ectx_item := AppRCtx tick.

  Definition translationKi (Ki : ectx_item) : ectx_item :=
    match Ki with
    | AppLCtx v2      => AppLCtx (translationV v2)
    | AppRCtx e1      => AppRCtx (tick $ translation e1)
    | UnOpCtx op      => UnOpCtx op
    | BinOpLCtx op v2 => BinOpLCtx op (translationV v2)
    | BinOpRCtx op e1 => BinOpRCtx op (tick $ translation e1)
    | IfCtx e1 e2     => IfCtx (translation e1) (translation e2)
    | PairLCtx v2     => PairLCtx (translationV v2)
    | PairRCtx e1     => PairRCtx (tick $ translation e1)
    | FstCtx          => FstCtx
    | SndCtx          => SndCtx
    | InjLCtx         => InjLCtx
    | InjRCtx         => InjRCtx
    | CaseCtx e1 e2   =>
        CaseCtx
          (tick_case_branch (λ: <>, translation e1))%E
          (tick_case_branch (λ: <>, translation e2))%E
    | AllocCtx        => AllocCtx
    | LoadCtx         => LoadCtx
    | StoreLCtx v2    => StoreLCtx (translationV v2)
    | StoreRCtx e1    => StoreRCtx (tick $ translation e1)
    | CasLCtx v0 v1   => CasLCtx (translationV v0) (translationV v1)
    | CasMCtx e1 v1   => CasMCtx (tick $ translation e1) (translationV v1)
    | CasRCtx e1 e2   => CasRCtx (tick $ translation e1) (translation e2)
    | FaaLCtx v2      => FaaLCtx (translationV v2)
    | FaaRCtx e1      => FaaRCtx (tick $ translation e1)
    end.

  Definition translationKi_aux (Ki : ectx_item) : ectx _ :=
    if ectx_item_is_active Ki then
      [ tickCtx ; translationKi Ki ]
    else
      [ translationKi Ki ].

  Definition translationK (K : ectx heap_ectx_lang) : ectx _ :=
    List.concat (translationKi_aux <$> K).

(*
 * Lemmas about translation
 *)

  Lemma translation_subst x e v :
    translation (subst x v e) = subst x (translationV v) (translation e).
  Proof.
    induction e ;
    unfold subst ; simpl ; fold subst ;
    try case_match ; (* ← this handles the cases of Var and Rec *)
    repeat f_equal ;
    assumption.
  Qed.

  Lemma translation_subst' x e v :
    translation (subst' x v e) = subst' x (translationV v) (translation e).
  Proof.
    destruct x.
    - reflexivity.
    - apply translation_subst.
  Qed.

  Lemma translation_injective :
    ∀ e1 e2,
      translation e1 = translation e2 →
      e1 = e2
  with translationV_injective :
    ∀ v1 v2,
      translationV v1 = translationV v2 →
      v1 = v2.
  Proof.
    destruct e1, e2; try discriminate; intros [=]; subst; f_equal;
      by (apply translation_injective || apply translationV_injective).
    destruct v1, v2; try discriminate; intros [=]; subst; f_equal;
      by (apply translation_injective || apply translationV_injective).
  Qed.

  Lemma translation_fill_item Ki e :
    translation (fill_item Ki e) = fill (translationKi_aux Ki) (translation e).
  Proof.
    destruct Ki ; reflexivity.
  Qed.

  Lemma translation_fill_item_active (ki : ectx_item) v :
    ectx_item_is_active ki →
    translation (fill_item ki v) = fill_item (translationKi ki) (tick (translationV v)).
  Proof.
    rewrite translation_fill_item.
    unfold translationKi_aux ; destruct (ectx_item_is_active ki) ; last contradiction.
    reflexivity.
  Qed.

  Lemma is_active_translationKi ki :
    ectx_item_is_active ki →
    ectx_item_is_active (translationKi ki).
  Proof.
    by destruct ki.
  Qed.

  Lemma translation_fill K e :
    translation (fill K e) = fill (translationK K) (translation e).
  Proof.
    revert e ; induction K ; intros e.
    - done.
    - rewrite /= fill_app - translation_fill_item //.
  Qed.

  Lemma lookup_translationS_None σ l :
    σ !! l = None →
    translationS σ !! l = None.
  Proof.
    intros H. by rewrite lookup_fmap H.
  Qed.

  Lemma lookup_translationS_Some σ l v :
    σ !! l = Some v →
    translationS σ !! l = Some (translationV v).
  Proof.
    intros H. by rewrite lookup_fmap H.
  Qed.

  Lemma lookup_translationS_is_Some σ l :
    is_Some (σ !! l) →
    is_Some (translationS σ !! l).
  Proof.
    destruct 1. eauto using lookup_translationS_Some.
  Qed.

  Lemma lookup_translationS_None_inv σ l :
    translationS σ !! l = None →
    σ !! l = None.
  Proof.
    unfold translationS ; rewrite lookup_fmap.
    destruct (σ !! l) eqn:E ; rewrite E ; first discriminate.
    done.
  Qed.

  Lemma lookup_translationS_Some_inv σ l v' :
    translationS σ !! l = Some v' →
    ∃ v,  σ !! l = Some v  ∧  v' = translationV v.
  Proof.
    rewrite lookup_fmap.
    destruct (σ !! l) eqn:E ; rewrite E ; last discriminate.
    intros ? % Some_inj ; eauto.
  Qed.

  Lemma lookup_translationS_is_Some_inv σ l :
    is_Some (translationS σ !! l) →
    is_Some (σ !! l).
  Proof.
    intros [_ (? & ? & _) % lookup_translationS_Some_inv]. eauto.
  Qed.

  Lemma translationS_insert l v σ :
    translationS (<[l := v]> σ) = <[l := translationV v]> (translationS σ).
  Proof.
    apply fmap_insert.
  Qed.

  Lemma un_op_eval_translation op v v' :
    un_op_eval op v = Some v' →
    un_op_eval op (translationV v) = Some (translationV v').
  Proof.
    intros H.
    destruct op ;
    destruct v ; try discriminate H ;
    simpl ; case_match ; simpl in *;
      try discriminate H;
      try match goal with
          |- context [to_mach_int ?x] => destruct (to_mach_int x); [|discriminate] end;
      try by injection H as <-.
  Qed.

  Local Lemma _eval_EqOp_bool_decide v1 v2 :
    bin_op_eval EqOp v1 v2 = Some $ LitV $ LitBool $ bool_decide (v1 = v2).
  Proof.
    destruct v1, v2 ; try done ;
    simpl ; case_match ; try done ;
    simpl ; case_match ; try done ;
    repeat f_equal ; apply bool_decide_iff ; naive_solver.
  Qed.

  Local Lemma _bool_decide_eq_translationV v1 v2 :
    bool_decide (v1 = v2) = bool_decide (translationV v1 = translationV v2).
  Proof.
    apply bool_decide_iff ; split ; intros H.
    - by rewrite H.
    - by eapply translationV_injective.
  Qed.

  Lemma bin_op_eval_translation op v1 v2 v' :
    bin_op_eval op v1 v2 = Some v' →
    bin_op_eval op (translationV v1) (translationV v2) = Some (translationV v').
  Proof.
    intros H.
    destruct op ; try (
      destruct v1, v2 ; try discriminate H ;
      unfold bin_op_eval in * ;
      do 3 try (case_match ; try discriminate H) ;
      simpl in *;
      try match goal with
          |- context [to_mach_int ?x] => destruct (to_mach_int x); [|discriminate] end;
      by injection H as <-
    ).
    (* Remaining case: op = EqOp *)
    rewrite _eval_EqOp_bool_decide in H ; injection H as <-.
    by rewrite _eval_EqOp_bool_decide - _bool_decide_eq_translationV.
  Qed.

  Lemma un_op_eval_translation_inv op v v' :
    un_op_eval op (translationV v) = Some v' →
    un_op_eval op v = Some v'.
  Proof.
    intros H.
    destruct op ;
    destruct v ; try discriminate H ;
    done.
  Qed.

  Lemma bin_op_eval_translation_inv op v1 v2 v' :
    bin_op_eval op (translationV v1) (translationV v2) = Some v' →
    bin_op_eval op v1 v2 = Some v'.
  Proof.
    intros H.
    destruct op ; try (
      destruct v1, v2 ; try discriminate H ;
      done
    ).
    (* Remaining case: op = EqOp *)
    rewrite -> _eval_EqOp_bool_decide in *. injection H as <-.
    by rewrite - _bool_decide_eq_translationV.
  Qed.

  Lemma translationV_lit lit :
    translationV #lit = #lit.
  Proof.
    done.
  Qed.

  Lemma translationV_lit_inv v lit :
    translationV v = #lit →
    v = #lit.
  Proof.
    destruct v ; try discriminate. done.
  Qed.

  Lemma vals_cas_compare_safe_translationV v1 v2 :
    vals_cas_compare_safe v1 v2 →
    vals_cas_compare_safe (translationV v1) (translationV v2).
  Proof.
    intros [].
    - left. by destruct v1 as [| | |[]|[]].
    - right. by destruct v2 as [| | |[]|[]].
  Qed.
  Lemma vals_cas_compare_safe_translationV_inv v1 v2 :
    vals_cas_compare_safe (translationV v1) (translationV v2) →
    vals_cas_compare_safe v1 v2.
  Proof.
    intros [].
    - left. by destruct v1 as [| | |[]|[]].
    - right. by destruct v2 as [| | |[]|[]].
  Qed.

End Translation.

(*
 * Notations
 *)

Notation "E« e »" := (translation e%E).
Notation "V« v »" := (translationV v%V).
Notation "Ki« ki »" := (translationKi ki).
Notation "K« K »" := (translationK K).
Notation "S« σ »" := (translationS σ%V).
Notation "T« t »" := (translation <$> t%E).

Notation "« e »" := (translation e%E).
Notation "« e »" := (translation e%E) : expr_scope.
Notation "« v »" := (translationV v%V) : val_scope.

(* for some reason, these notations make parsing fail,
 * even if they only regard printing… *)
(*
Notation "« e »" := (translation e%E) (only printing).
Notation "« v »" := (translationV v%V) (only printing).
Notation "« ki »" := (translationKi ki) (only printing).
Notation "« K »" := (translationK K) (only printing).
Notation "« σ »" := (translationS σ%V) (only printing).
Notation "« t »" := (translation <$> t%E) (only printing).
*)

(* FIXME : the way coercions should or should not be included in
   notations so that notations are pretty-printed back is completely
   non-predictible. *)

Notation "'tickrec:' f x y .. z := e" :=
  (tick (Rec f%bind x%bind (tick (Lam y%bind .. (tick (Lam z%bind e%E)) ..))))
  (at level 200, f, x, y, z at level 1, e at level 200,
   format "'[' 'tickrec:'  f  x  y  ..  z  :=  '/  ' e ']'") : expr_scope.

Notation "tickλ: x , e" := (tick (Lam x%bind e%E))
  (at level 200, x at level 1, e at level 200,
   format "'[' 'tickλ:'  x ,  '/  ' e ']'") : expr_scope.
Notation "tickλ: x y .. z , e" :=
  (tick (Lam x%bind (tick (Lam y%bind .. (tick (Lam z%bind e%E)) ..))))
  (at level 200, x, y, z at level 1, e at level 200,
   format "'[' 'tickλ:'  x  y  ..  z ,  '/  ' e ']'") : expr_scope.

Notation "'lettick:' x := e1 'in' e2" :=
  ((tick (App (Val tick) (Lam x%bind e2%E))) e1%E)
  (at level 200, x at level 1, e1, e2 at level 200,
   format "'[' 'lettick:'  x  :=  '[' e1 ']'  'in'  '/' e2 ']'") : expr_scope.

Notation "e1 ;tick; e2" :=
  ((tick (App (Val tick) (Lam BAnon e2%E))) e1%E)
  (at level 100, e2 at level 200,
   format "'[' '[hv' '[' e1 ']'  ;tick;  ']' '/' e2 ']'") : expr_scope.

Notation "'tickmatch:' e0 'with' 'InjL' x1 => e1 | 'InjR' x2 => e2 'end'" :=
  (Case (App (Val tick) e0) (App (Val tick_case_branch) (λ: <>, App (Val tick) (λ: x1, e1))%E)
                            (App (Val tick_case_branch) (λ: <>, App (Val tick) (λ: x2, e2))%E))
  (e0, x1, e1, x2, e2 at level 200,
   format "'[hv' 'tickmatch:'  e0  'with'  '/  ' '[' 'InjL'  x1  =>  '/  ' e1 ']'  '/' '[' |  'InjR'  x2  =>  '/  ' e2 ']'  '/' 'end' ']'") : expr_scope.

(*
  Typeclass instance for the proofmode
 *)

Instance AsRecV_translationV `{Tick} v f x e :
  AsRecV v f x e →
  AsRecV « v » f x « e ».
Proof. by intros ->. Qed.

(*
 * Simplification tactic
 *)

(* simpl and cbn do not work well with mutual fixpoints... *)
Ltac simpl_trans :=
  cbn [translation translationV]; fold translation translationV.

(*
 * (Partial) Inverse translation
 *)

Section InvTranslation.

  Fixpoint invtranslation (e : expr) : expr :=
    match e with
    (* Concurrency -- This pattern has to appear before the pattern of
      App, since it conflicts with it. *)
    | App tick (Fork e)          => Fork (invtranslation e)
    (* Base lambda calculus *)
    | Var _                      => e
    | App tick (Rec f x e)       => Rec f x (invtranslation e)
    | App (App tick e1) e2       => (invtranslation e1) (invtranslation e2)
    | Val v                      => Val (invtranslationV v)
    (* Base types and their operations *)
    | UnOp op (App tick e)       => UnOp op (invtranslation e)
    | BinOp op (App tick e1) e2  => BinOp op (invtranslation e1) (invtranslation e2)
    | If (App tick e0) e1 e2     => If (invtranslation e0) (invtranslation e1) (invtranslation e2)
    (* Products *)
    | Pair (App tick e1) e2      => Pair (invtranslation e1) (invtranslation e2)
    | Fst (App tick e)           => Fst (invtranslation e)
    | Snd (App tick e)           => Snd (invtranslation e)
    (* Sums *)
    | InjL (App tick e)          => InjL (invtranslation e)
    | InjR (App tick e)          => InjR (invtranslation e)
    | Case (App tick e0) (App tickaux1 (Rec BAnon BAnon e1)) (App tickaux2 (Rec BAnon BAnon e2)) =>
        Case (invtranslation e0) (invtranslation e1) (invtranslation e2)
    (* Heap *)
    | Alloc (App tick e)         => Alloc (invtranslation e)
    | Load (App tick e)          => Load (invtranslation e)
    | Store (App tick e1) e2     => Store (invtranslation e1) (invtranslation e2)
    | CAS (App tick e0) e1 e2    => CAS (invtranslation e0) (invtranslation e1) (invtranslation e2)
    | FAA (App tick e1) e2       => FAA (invtranslation e1) (invtranslation e2)
    | _ => #42
    end %E
  with invtranslationV v :=
    match v with
    | RecV f x e    => RecV f x (invtranslation e)
    | LitV _        => v
    | PairV v1 v2   => PairV (invtranslationV v1) (invtranslationV v2)
    | InjLV v       => InjLV (invtranslationV v)
    | InjRV v       => InjRV (invtranslationV v)
    end.

  Lemma invtranslation_translation {Htick : Tick} e :
    invtranslation (translation e) = e
  with invtranslationV_translationV {Htick : Tick} v :
    invtranslationV (translationV v) = v.
  Proof.
    - specialize (invtranslation_translation Htick).
      specialize (invtranslationV_translationV Htick).
      destruct e;
        try by rewrite /= ?invtranslation_translation ?invtranslationV_translationV.
      (* Handle the App case by hand. *)
      { simpl. rewrite !invtranslation_translation. case_match=>//.
          by destruct e2. by destruct e2. }

    - specialize (invtranslation_translation Htick).
      specialize (invtranslationV_translationV Htick).
      destruct v;
        try by rewrite /= ?invtranslation_translation ?invtranslationV_translationV.
  Qed.
End InvTranslation.



(*
 * Characterizing expressions that are left invariant by translation
 *)

Section ClosureFree.

  Fixpoint closure_free (v : val) : bool :=
    match v with
    | RecV _ _ _ => false
    | LitV _ => true
    | PairV v1 v2 => closure_free v1 && closure_free v2
    | InjLV v1 => closure_free v1
    | InjRV v1 => closure_free v1
    end.

  Lemma closure_free_is_translationV_invariant {Htick : Tick} v :
    closure_free v →
    translationV v = v.
  Proof.
    intros ?.
    induction v as
      [ (* LitV *) lit
      | (* RecV *) f x e1
      | (* PairV *) v1 IH1 v2 IH2
      | (* InjLV *) v1 IH1
      | (* InjRV *) v1 IH1
      ] ; cbn in *.
    - done.
    - contradiction.
    - rewrite IH1 ?IH2; naive_solver.
    - rewrite IH1 ; naive_solver.
    - rewrite IH1 ; naive_solver.
  Qed.

  Lemma closure_free_is_invtranslationV_invariant v :
    closure_free v →
    invtranslationV v = v.
  Proof.
    intros ?.
    induction v as
      [ (* LitV *) lit
      | (* RecV *) f x e1
      | (* PairV *) v1 IH1 v2 IH2
      | (* InjLV *) v1 IH1
      | (* InjRV *) v1 IH1
      ] ; cbn.
    - done.
    - contradiction.
    - rewrite -> IH1, IH2 ; naive_solver.
    - rewrite IH1 ; naive_solver.
    - rewrite IH1 ; naive_solver.
  Qed.

  Lemma closure_free_translationV {Htick : Tick} v :
    closure_free v →
    closure_free (translationV v).
  Proof.
    intros Hv. by rewrite (closure_free_is_translationV_invariant v Hv).
  Qed.

  Lemma closure_free_invtranslationV v :
    closure_free v →
    closure_free (invtranslationV v).
  Proof.
    intros Hv. by rewrite (closure_free_is_invtranslationV_invariant v Hv).
  Qed.

  Lemma closure_free_translationV_iff  {Htick : Tick} v :
    closure_free v  ↔  closure_free (translationV v).
  Proof.
    split.
    - apply closure_free_translationV.
    - intros H % closure_free_invtranslationV. by rewrite invtranslationV_translationV in H.
  Qed.

  Lemma closure_free_predicate (φ : val → Prop) :
    (∀ (v : val), φ v → closure_free v) →
    ∀ (v : val),
      φ v → φ (invtranslationV v).
  Proof.
    intros Hφ v H.
    by specialize (Hφ _ H) as -> % closure_free_is_invtranslationV_invariant.
  Qed.

End ClosureFree.

(*
 *  Proofmode wp_* tactics.
 *)

(* wp_tick is a stub to be redefined for each particular definition of
   the tick function. *)
Ltac wp_tick := idtac.

Ltac wp_tick_closure := wp_closure; wp_tick.
Ltac wp_tick_pair := wp_tick; wp_pair.
Ltac wp_tick_inj := wp_tick; wp_inj.

Ltac wp_tick_rec := wp_tick ; wp_rec; simpl_trans.
Ltac wp_tick_lam := wp_tick_rec.
Ltac wp_tick_let := wp_tick_closure; wp_tick_lam.
Ltac wp_tick_seq := wp_tick_let.
Ltac wp_tick_op := wp_tick ; wp_op.
Ltac wp_tick_if := wp_tick ; wp_if.
Ltac wp_tick_match :=
  wp_tick; wp_match; (wp_let || wp_seq); wp_lam;
  wp_closure; wp_tick; wp_tick; wp_lam.
Ltac wp_tick_proj := wp_tick ; wp_proj.
Ltac wp_tick_alloc loc := wp_tick ; wp_alloc loc.
Ltac wp_tick_load := wp_tick ; wp_load.
Ltac wp_tick_store := wp_tick ; wp_store.
