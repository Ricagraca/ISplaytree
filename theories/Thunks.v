From stdpp Require Import namespaces.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import auth excl agree csum.
From iris_time.heap_lang Require Import proofmode notation.
From iris_time Require Import TimeCredits Auth_max_nat.

(*
  This file contains a formalization of thunks. Compared with ThunksSimple.v,
  it specifies the same HeapLang code, but the representation predicate is more
  involved, so that we can also:

    - prove that a thunk always return the same value (the user of the library
      could already do that, but it comes for free as a by-product of our
      internal ghost state),
    - prove the consequence rule (see below),
    - and pass additional (non-persistent) assertions to the suspended code.

  Postconditions of thunks are necessarily persistent.

  The consequence rule is roughly the following: if we have a thunk with debt n
  and postcondition φ, and we can update φ to ψ by also spending m time credits
  (that is, TC m ∗ φ ==∗ ψ) where both φ and ψ are persistent, then we can see
  the thunk as having debt (n+m) and postcondition ψ.

      Thunk t  n    φ        TC m ∗ φ ==∗ ψ
      =====================================∗   CONSEQUENCE
      Thunk t (n+m) ψ

  The idea is that, when forcing the thunk, not only we consume n time credits
  to run the suspended code once and get its postcondition φ, we also consume
  m time credits to “run” the ghost update once and get ψ from φ.

  It is the combination of two desirable rules:

      Thunk t  n     φ
      ==============================∗   BORROWING
      Thunk t (n+m) (φ ∗ TC m)          (* nonsensical, postcond must be persistent *)

      Thunk t n φ            φ ==∗ ψ
      ==============================∗   CONSEQUENCE'
      Thunk t n ψ

  The consequence rule allows to reason about chained thunks. Combined with the
  pay rule applied to the inner thunk, it allows to derive the following:

      Thunk t1  n1    (λ t2, Thunk t2  n2    φ)
      =========================================∗    FORWARDING OF DEBT
      Thunk t1 (n1+m) (λ t2, Thunk t2 (n2-m) φ)

  To rule out reentrency, we still have one token per thunk, which is required
  to force the thunk. To be able to force a thunk that forces a thunk, we need
  to pass the token of the inner thunk to the code suspended by the outer thunk.
  We do so by allowing to pass an arbitrary assertion R during forcing (R is
  recovered after forcing).

  Variables:

    - p: thread pool name (technical detail)
    - t: physical location of the thunk
    - γv: ghost name given to the thunk (technical detail)
    - n: apparent remaining debt (might be over-estimated)
    - R: assertion to pass to the suspended code when forcing (recovered afterwards)
    - φ: persistent predicate about the value computed by forcing
    - v: the computed value of the thunk

  Provided assertions:

    - Thunk p t γv n R φ : persistent representation predicate
    - ThunkVal γv v      : persistent assertion saying that thunk t/γv has been
                           forced and that its value is v
    - ThunkToken p t     : unique token required to force thunk t

  The representation predicate Thunk is defined inductively.

    - The “base” thunk predicate represents the bare thunk: it stores the
      physical location of the thunk.
    - A “consequence” thunk predicate is the pair of (1) a parent thunk predicate
      about the same thunk, and (2) a consequence rule to apply to this parent.

  Using the CONSEQUENCE rule, as defined earlier, simply consists in logically
  building a consequence thunk predicate on top of the provided thunk predicate.

  Thus, thunk predicates about a given thunk are the “nodes” of a tree.
  Each node stores either an operation to be performed once (when forcing),
  or the result of this operation (if already forced).

    - The base node corresponds to the physical execution of the suspended code.
      It stores either the triple for this code, or its postcondition.
    - A consequence node corresponds to the logical execution of a ghost update.
      It stores either this ghost update, or its conclusion.

  All of these operations have their own cost in time credits. The cumulated
  cost of all operations, from the base node up to the considered descendent, is
  the debt of this descendent. The user can logically reduce the debt by paying,
  i.e. storing time credits in the thunk. Each node has its own deposit, storing
  only the time credits needed for its own operation.

  Only when the debt of a node is zero, the user can physically “force” the
  thunk, i.e. evaluate it.

  Note that, when forcing a node, only this node and its ancestors, down until
  the base node, are forced. Siblings or descendents are not. So even if we know
  that we have forced some node about a thunk t already, we cannot use that
  knowledge when considering some other node about t. In fact, it is possible
  that the other node still has a non-zero debt because we haven’t paid for the
  additional consequences yet. The only thing we know is that the base node has
  indeed been forced.
 *)

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

Section ThunkProofs.

  Notation valO := (valO heap_lang).
  Context `{timeCreditHeapG Σ}.
  Context `{inG Σ (csumR (exclR unitO) (agreeR valO))}. (* γv *)
  Context `{inG Σ (authR $ optionUR $ exclR boolO)}.    (* γforced *)
  Context `{inG Σ (authR max_natUR)}.                   (* γpaid *)
  Context `{na_invG Σ}.

  Implicit Type t : loc.
  Implicit Type f v : val.
  Implicit Type γv γforced γpaid : gname.
  Implicit Type forced : bool.
  Implicit Type n m paid k : nat.
  Implicit Type R : iProp Σ.
  Implicit Type φ ψ : val → iProp Σ.
  Implicit Type d : nat.
  Implicit Type p : na_inv_pool_name.
  Implicit Type E F : coPset.

  Definition thunkN t : namespace :=
    nroot .@ "thunk" .@ t.
  Definition thunkPaidN t : namespace :=
    thunkN t .@ "paid".
  Definition thunkAtDepthN t d : namespace :=
    thunkN t .@ "depth" .@ d.

  Notation ThunkToken p t := (na_own p (↑thunkN t)).

  Notation ThunkVal γv v := (own γv (Cinr $ to_agree v)).

  Definition ThunkBaseInv t γv γforced n R φ : iProp Σ := (
    ∃ forced,
        own γforced (● Excl' forced)
      ∗ if forced then
          ∃ v,
              t ↦ EVALUATEDV « v »
            ∗ own γv (Cinr $ to_agree v)
            ∗ □ φ v
        else
          ∃ f,
              t ↦ UNEVALUATEDV « f »
            ∗ own γv (Cinl $ Excl ())
            ∗ (TC n -∗ R -∗ ∀ ψ, (∀ v, R -∗ □ φ v -∗ ψ «v»%V) -∗ WP «f #()» {{ ψ }})
  )%I.
  Definition ThunkCsqInv t γv γforced n φ ψ : iProp Σ := (
    ∃ forced,
        own γforced (● Excl' forced)
      ∗ if forced then
          ∃ v, own γv (Cinr $ to_agree v) ∗ □ ψ v
        else
          ∀ v, TC n -∗ φ v ={⊤}=∗ □ ψ v
  )%I.
  Definition ThunkPaidInv t γforced γpaid : iProp Σ := (
    ∃ forced paid,
        own γforced (◯ Excl' forced)
      ∗ own γpaid (● MaxNat paid)
      ∗ if forced then True else TC paid
  )%I.
  Fixpoint Thunk' p t γv n R φ d : iProp Σ := (
    ∃ γforced γpaid paid m,
        ⌜paid ≤ m ≤ n+paid⌝
      ∗ own γpaid (◯ MaxNat paid)
      ∗ inv (thunkPaidN t) (ThunkPaidInv t γforced γpaid)
      ∗ match d with
        | 0 =>
            na_inv p (thunkAtDepthN t 0) (ThunkBaseInv t γv γforced m R φ)
        | S d' =>
            ∃ φ',
                Thunk' p t γv (n+paid-m) R φ' d'
              ∗ na_inv p (thunkAtDepthN t d) (ThunkCsqInv t γv γforced m φ' φ)
        end
  )%I.
  Definition Thunk p t γv n R φ : iProp Σ := (
    ∃ d, Thunk' p t γv n R φ d
  )%I.

  Lemma ThunkToken_exclusive p t1 t2 :
    ThunkToken p t1 -∗ ThunkToken p t2 -∗ ⌜t1 ≠ t2⌝.
  Proof.
    iIntros "H1 H2" (<-). iDestruct (na_own_disjoint with "H1 H2") as %Hdisj.
    exfalso. apply (nclose_infinite (thunkN t1)).
    rewrite (_ : ↑thunkN t1 = ∅) ; last set_solver. apply empty_finite.
  Qed.

  Lemma ThunkVal_persistent γv v :
    Persistent (ThunkVal γv v).
  Proof. exact _. Qed.

  Lemma ThunkVal_agree γv v1 v2 :
    ThunkVal γv v1 -∗ ThunkVal γv v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "H1 H2". iDestruct (own_valid_2 with "H1 H2") as %Hag. iPureIntro.
    eapply to_agree_op_valid_L, (proj1 (Cinr_valid (A:=unitR) _)). by rewrite Cinr_op.
  Qed.

  Instance Thunk'_persistent p t γv n R φ d :
    Persistent (Thunk' p t γv n R φ d).
  Proof.
    revert n φ. induction d ; exact _.
  Qed.

  Lemma Thunk_persistent p t γv n R φ :
    Persistent (Thunk p t γv n R φ).
  Proof. exact _. Qed.

  Lemma Thunk_weaken p t γv n₁ n₂ R φ :
    (n₁ ≤ n₂)%nat →
    Thunk p t γv n₁ R φ -∗
    Thunk p t γv n₂ R φ.
  Proof.
    iIntros (I) "H". iDestruct "H" as (d) "H". iExists d.
    iInduction (d) as [|d'] "IH" forall (n₁ n₂ I φ).
    { iDestruct "H" as (γforced γpaid paid m) "(%&H)".
      iExists γforced, γpaid, paid, m. iFrame "H". iPureIntro. lia. }
    { iDestruct "H" as (γforced γpaid paid m) "(%&?&?&H)"; fold Thunk'.
      iDestruct "H" as (φ') "[??]".
      iExists γforced, γpaid, paid, m; fold Thunk'. iFrame. iSplit ; first (iPureIntro;lia).
      iExists φ'. iFrame. iApply ("IH" with "[] [$]"). iPureIntro. lia. }
  Qed.

  Lemma Thunk_consequence p t γv n m R φ ψ :
    (∀ v, TC m -∗ φ v ={⊤}=∗ □ ψ v) -∗
    Thunk p t γv  n    R φ  ={∅}=∗
    Thunk p t γv (n+m) R ψ.
  Proof.
    iIntros "Hφψ Ht".
    iDestruct "Ht" as (d) "Ht".
    iMod (own_alloc (● MaxNat 0 ⋅ ◯MaxNat 0)) as (γpaid) "[Hγpaid● Hγpaid◯]".
    { by apply auth_both_valid_2. }
    iMod (own_alloc (● Excl' false ⋅ ◯ Excl' false)) as (γforced) "[Hγforced● Hγforced◯]".
    { by apply auth_both_valid_2. }
    iExists (S d), γforced, γpaid, 0, m; fold Thunk'. iFrame "Hγpaid◯".
    iSplitR ; last iSplitR "Ht Hγforced● Hφψ".
    { iPureIntro;lia. }
    { iMod zero_TC. iApply inv_alloc. iExists false. iFrame. iExists 0. by iFrame. }
    { iExists φ. rewrite (_ : n+m+0-m = n) ; last lia. iFrame "Ht".
      iApply na_inv_alloc. iExists false. by iFrame. }
  Qed.

  Lemma Thunk_pay_ind_aux E t γforced γpaid paid k m n :
    ↑thunkPaidN t ⊆ E →
        ⌜paid ≤ m ≤ n+paid⌝
      ∗ inv (thunkPaidN t) (ThunkPaidInv t γforced γpaid)
      ∗ own γpaid (◯ MaxNat paid)
      ∗ TC k
    ={E}=∗
      let paying := k `min` (m - paid) in
      let paid2 := paid + paying in
        ⌜paid2 ≤ m ≤ (n-k)+paid2⌝
      ∗ own γpaid (◯ MaxNat paid2)
      ∗ TC (k-paying).
  Proof.
      set paying := k `min` (m - paid).
      iIntros (?) "(% & HpaidInv & Hγpaid◯ & Htc)".
      iSplitR ; first (iPureIntro;lia).
      rewrite [in TC k](_ : k = (k-paying) + paying) ; last lia. iDestruct "Htc" as "[$ Htc]".
      iMod (inv_acc with "HpaidInv") as "[HpaidInv HpaidInvClose]" ; first done.
      iDestruct "HpaidInv" as (forced paid') "(Hγforced◯ & >Hγpaid● & Hpaid)".
      iMod (auth_max_nat_update_incr' _ _ _ paying with "Hγpaid● Hγpaid◯")
        as "[Hγpaid● $]" ; simpl.
      iApply "HpaidInvClose". iExists forced, (paid' + paying). iFrame. destruct forced.
      - done.
      - by iSplitR "Htc".
  Qed.

  Lemma Thunk_pay_ind E p t γv n k R φ d :
    ↑thunkPaidN t ⊆ E →
    TC k -∗ Thunk' p t γv n R φ d ={E}=∗ Thunk' p t γv (n-k) R φ d.
  Proof.
    (* proof by induction on the depth d of the predicate: *)
    iIntros (?) "Htc Ht". iInduction (d) as [|d'] "IH" forall (n k φ).
    (* (1) base case: the “node” at hand actually stores the thunk. *)
    {
      (* store as much credit as possible in the base node: *)
      iDestruct "Ht" as (γforced γpaid paid m) "(? & ? & #? & ?)".
      set paying := k `min` (m - paid).
      iExists γforced, γpaid, (paid + paying), m. iFrame "#∗".
      by iDestruct (Thunk_pay_ind_aux with "[$]") as ">($ & $ & _)".
      (* nothing else to do *)
    }
    (* (2) consequence case: the “node” at hand stores a consequence to apply. *)
    {
      (* store as much credit as possible in the current node: *)
      iDestruct "Ht" as (γforced γpaid paid m) "(? & ? & #? & H)" ; fold Thunk'.
      set paying := k `min` (m - paid).
      iExists γforced, γpaid, (paid + paying), m ; fold Thunk'. iFrame "#".
      iDestruct (Thunk_pay_ind_aux with "[$]") as ">(% & $ & Htc)" ; first done.
      fold paying. iSplitR ; first (iPureIntro;lia).
      (* pay recursively with the remainder, by applying the induction hypothesis: *)
      iDestruct "H" as (φ') "[Ht ?]". iExists φ'. iFrame.
      rewrite (_ : n-k+(paid+paying)-m = (n+paid-m) - (k-paying)) ; last lia.
      by iApply ("IH" with "Htc Ht").
    }
  Qed.

  Lemma Thunk_pay E p t γv n k R φ :
    ↑thunkPaidN t ⊆ E →
    TC k -∗ Thunk p t γv n R φ ={E}=∗ Thunk p t γv (n-k) R φ.
  Proof.
    iIntros (?) "Htc Ht". iDestruct "Ht" as (d) "Ht". iExists d.
    by iApply (Thunk_pay_ind with "Htc Ht").
  Qed.

  Lemma create_spec p n R φ f :
    TC_invariant -∗
    {{{ TC 3 ∗ ( TC n -∗ R -∗ ∀ ψ, (∀ v, R -∗ □ φ v -∗ ψ «v»%V) -∗ WP «f #()» {{ ψ }} ) }}}
    « create f »
    {{{ t γv, RET #t ; Thunk p t γv n R φ }}}.
  Proof.
    iIntros "#HtickInv" (Φ) "!# [? Hf] Post".
    iMod (own_alloc (Cinl $ Excl ())) as (γv) "?" ; first done.
    iMod (own_alloc (● MaxNat 0 ⋅ ◯MaxNat 0)) as (γpaid) "[Hγpaid● Hγpaid◯]".
    { by apply auth_both_valid_2. }
    iMod (own_alloc (● Excl' false ⋅ ◯ Excl' false)) as (γforced) "[Hγforced● Hγforced◯]".
    { by apply auth_both_valid_2. }
    iApply wp_fupd. wp_tick_lam. wp_tick_inj. wp_tick_alloc t. iApply "Post".
    iExists 0, γforced, γpaid, 0, n. iFrame. iSplitR ; first (iPureIntro;lia).
    iSplitL "Hγpaid● Hγforced◯".
    { iMod zero_TC. iApply inv_alloc. iExists false. iFrame. iExists 0. by iFrame. }
    { iApply na_inv_alloc. iExists false. auto with iFrame. }
  Qed.

  Lemma take_paid_from_ThunkPaidInv E t γforced γpaid m :
    ↑thunkPaidN t ⊆ E →
    inv (thunkPaidN t) (ThunkPaidInv t γforced γpaid) -∗
    own γforced (● Excl' false) -∗
    own γpaid (◯ MaxNat m) -∗
    |={E}=>
      own γforced (● Excl' true)
    ∗ TC m.
  Proof.
    iIntros (?) "HpaidInv Hγforced● Hγpaid◯".
    (* get the m accumulated time credits, by opening the “paid” invariant: *)
    iMod (inv_acc with "HpaidInv") as "[HpaidInv HpaidInvClose]" ; first done.
    iDestruct "HpaidInv" as (forced paid) "(>Hγforced◯ & >Hγpaid● & Hpaid)".
    iAssert ⌜forced = false⌝%I as %->.
    { by iDestruct (own_valid_2 with "Hγforced● Hγforced◯")
        as %[[=]%Excl_included ]%auth_both_valid_discrete. }
    iDestruct (own_auth_max_nat_le with "Hγpaid● Hγpaid◯") as %Hle; cbn in Hle.
    iDestruct (TC_weaken _ _ Hle with "Hpaid") as ">Hm".
    (* update the ghost state to b = true, so as to switch both invariants
     * to the other side: *)
    iMod (own_update_2 with "Hγforced● Hγforced◯") as "Hγforced".
    { by apply auth_update, option_local_update, (exclusive_local_update _ (Excl true)). }
    iDestruct "Hγforced" as "[Hγforced● Hγforced◯]".
    (* close the “paid” invariant: *)
    iMod ("HpaidInvClose" with "[Hγforced◯ Hγpaid●]"). { iExists true, paid. by iFrame. }
    by iFrame.
  Qed.

  Lemma force_spec_ind p F t γv R φ d :
    (∀ d', d' ≤ d  →  ↑thunkAtDepthN t d' ⊆ F) →
    TC_invariant -∗
    {{{ TC 11
      ∗ Thunk' p t γv 0 R φ d
      ∗ na_own p F
      ∗ R
    }}}
    « force #t »
    {{{ v, RET «v» ;
        own γv (Cinr $ to_agree v)
      ∗ □ φ v
      ∗ na_own p F
      ∗ R
    }}}.
  Proof.
    iIntros (HF) "#HtickInv".
    iIntros (Φ) "!> (Htc & Ht & Hp & HR) Post".
    (* proof by induction on the depth d of the predicate: *)
    iInduction (d) as [|d' IH] "IH" forall (F HF φ Φ).
    (* (1) base case: the “node” at hand actually stores the thunk. *)
    {
      iDestruct "Ht" as (γforced γpaid paid m) "(% & Hγpaid◯ & HpaidInv & #HtInv)"; fold Thunk'.
      (* open the “base” invariant: *)
      wp_tick_lam.
      iDestruct (na_inv_acc with "HtInv Hp") as ">(Ht & Hp & HtInvClose)" ;
        [done|auto|].
      (* add a fupd so that we can close it at the end: *)
      iApply wp_fupd.
      (* case analysis on whether the thunk has been forced already: *)
      iDestruct "Ht" as ([|]) "[Hγforced● H]".
      (* (1a) if forced = true: *)
      {
        (* get the memoized value and the already computed postcondition: *)
        iDestruct "H" as (v) "(Ht & #Hγv & #Hφ)".
        wp_tick_load. wp_tick_match.
        iApply "Post". iFrame "#∗".
        (* close the “base” invariant: *)
        iApply "HtInvClose". iFrame. iExists true. iFrame. iExists v. by iFrame "#∗".
      }
      (* (1b) if forced = false: *)
      {
        wp_tick.
        (* get the m accumulated time credits, by opening the “paid” invariant: *)
        assert (paid = m) as -> by lia.
        iDestruct (take_paid_from_ThunkPaidInv with "[$][$][$]") as ">[Hγforced● Hm]" ; first done.
        (* perform the forcing, obtain the value and the postcondition: *)
        iDestruct "H" as (f) "(Ht & Hγv & Hf)".
        wp_load. wp_tick_match.
        wp_apply ("Hf" with "Hm HR"). iIntros (v) "HR #Hφ".
        wp_tick_let. wp_tick_inj. wp_tick_store. wp_tick_seq.
        iApply "Post". iFrame "#∗".
        (* update the ghost state to remember that the value has been computed: *)
        iDestruct (own_update _ _ (Cinr $ to_agree v) with "Hγv") as ">#$".
        { by apply cmra_update_exclusive. }
        (* close the “base” invariant: *)
        iApply "HtInvClose". iFrame. iExists true. iFrame. iExists v. by iFrame "#∗".
      }
    }
    (* (2) consequence case: the “node” at hand stores a consequence to apply. *)
    {
      iDestruct "Ht" as (γforced γpaid paid m) "(% & Hγpaid◯ & HpaidInv & H)"; fold Thunk'.
      iDestruct "H" as (φ') "[Ht HcsqInv]".
      rewrite (_ : 0+paid-m = 0) ; last lia.
      set d := S d' in HF |- *.
      (* open the “consequence” invariant: *)
      rewrite (_ : F = ↑thunkAtDepthN t d ∪ (F ∖ ↑thunkAtDepthN t d)) ;
        first setoid_rewrite na_own_union ;
        [ | set_solver | set_solver | apply union_difference_L ; by auto ].
      iDestruct "Hp" as "[Hpd Hp]".
      iDestruct (na_inv_acc with "HcsqInv Hpd") as ">(HcsqInv & Hp' & HcsqInvClose)" ;
        [done|done|].
      (* add a fupd so that we can close it at the end: *)
      iApply wp_fupd.
      (* apply the induction hypothesis, get the value and the postcondition: *)
      iApply ("IH" with "[] Htc Ht Hp HR") ; iClear "HtickInv IH".
      { iPureIntro ; intros d1 ?.
        assert (d1 ≤ d  ∧  d1 ≠ d) as [??] by lia. solve_ndisj. }
      iIntros (v) "!>(#Hγv & Hφ' & Hp & HR)". iApply "Post". iFrame "#∗".
      (* case analysis on whether this node has been forced already: *)
      iDestruct "HcsqInv" as ([|]) "[Hγforced● Hcsq]".
      (* (2a) if forced = true: *)
      {
        (* get the result of the already computed consequence: *)
        iDestruct "Hcsq" as (v') "[Hγv' #Hφ]".
        iDestruct (ThunkVal_agree with "Hγv Hγv'") as %<-.
        iFrame "#".
        (* close the “consequence” invariant: *)
        iApply "HcsqInvClose". iFrame. iExists true. iFrame. iExists v. by iFrame "#".
      }
      (* (2b) if forced = false: *)
      {
        (* get the m accumulated time credits, by opening the “pay” invariant: *)
        assert (paid = m) as -> by lia.
        iDestruct (take_paid_from_ThunkPaidInv with "[$][$][$]") as ">[Hγforced● Hm]" ; first done.
        (* compute the consequence: *)
        iDestruct ("Hcsq" $! v with "Hm Hφ'") as ">#$".
        (* close the “consequence” invariant: *)
        iApply "HcsqInvClose". iFrame. iExists true. iFrame. iExists v. by iFrame "#".
      }
    }
  Qed.

  Lemma force_spec p t γv R φ :
    TC_invariant -∗
    {{{ TC 11 ∗ Thunk p t γv 0 R φ ∗ ThunkToken p t ∗ R }}}
    « force #t »
    {{{ v, RET «v» ; ThunkVal γv v ∗ □ φ v ∗ ThunkToken p t ∗ R }}}.
  Proof.
    iIntros "#HtickInv" (Φ) "!>(Htc & Ht & Hp & HR) Post".
    iDestruct "Ht" as (d) "Ht".
    wp_apply (force_spec_ind with "HtickInv [-Post] Post") ; first solve_ndisj.
    by iFrame.
  Qed.

  (* The following is provable. It amounts to forcing logically the thunk,
     knowing that the base node has already been forced and has value v.
     However the proof would largely replicate that of force_spec, and this
     reasoning rule does not seem useful in practice. *)
  Lemma ThunkVal_force p t γv R φ v :
    Thunk p t γv 0 R φ -∗
    ThunkVal γv v -∗
    ThunkToken p t -∗
    |={⊤}=>
      ▷ □ φ v ∗ ThunkToken p t.
  Abort.

  (* Example: forwarding of debt for a thunk that creates a thunk: *)
  Goal ∀ p t1 γv1 n1 n2 m R φ,
    Thunk p t1 γv1 n1 R (λ v2, ∃ t2 γv2, ⌜v2 = #t2⌝ ∗
      Thunk p t2 γv2 n2 R φ
    )
    ={∅}=∗
    Thunk p t1 γv1 (n1+m) R (λ v2, ∃ t2 γv2, ⌜v2 = #t2⌝ ∗
      Thunk p t2 γv2 (n2-m) R φ
    ).
  Proof.
    iIntros. iApply Thunk_consequence=>//.
    iIntros (v2) "Htc Ht2" ; iDestruct "Ht2" as (t2 γv2) "[#? Ht2]".
    iExists t2, γv2. iFrame "#". by iMod (Thunk_pay with "Htc Ht2") as "#$".
  Qed.

  (* Example: creating a thunk that forces a thunk: *)
  Goal ∀ p t2 γv2 n2 R φ,
    TC_invariant -∗
    {{{ TC 3 ∗ Thunk p t2 γv2 n2 R φ }}}
    « create (λ: <>, force #t2)%V »
    {{{ t1 γv1, RET #t1 ;
      Thunk p t1 γv1 (12+n2) (ThunkToken p t2 ∗ R) (λ v,
          (*ThunkVal γv1 v (* note: we cannot speak about t1 here, because it is not known before create *)
        ∗*) ThunkVal γv2 v
        ∗ □ φ v
      )
    }}}.
  Proof.
    intros ; iIntros "#HtickInv" (?) "!> [Htc Ht2] Post".
    wp_apply (create_spec with "HtickInv [$Htc Ht2] Post").
    iIntros "[Htc1 Htc2] [Htok2 HR]" (Ψ) "Post".
    iMod (Thunk_pay with "Htc2 Ht2") as "Ht2" ; first done. rewrite Nat.sub_diag.
    wp_tick_lam. wp_apply (force_spec with "HtickInv [$]").
    iIntros (v) "(#Htv2 & #Hφ & Htok2 & HR)". by iApply ("Post" with "[$] [$]").
  Qed.

End ThunkProofs.
