From TLC Require Import LibTactics LibLogic LibSet LibRelation LibFun LibEqual
                        LibInt.
From iris_time.union_find.math Require Import TLCBuffer.

From stdpp Require Import gmap.

From iris.bi Require Import big_op.
From iris_time.heap_lang Require Import proofmode.
From iris_time Require Import Combined.

(* Load extra math libraries. *)
From iris_time.union_find.math Require Import LibNatExtra InverseAckermann.
(* Load the mathematical analysis of UnionFind. *)
From iris_time.union_find.math Require Import UnionFind01Data
     UnionFind02EmptyCreate UnionFind03Link UnionFind04Compress
     UnionFind05IteratedCompression UnionFind06Join UnionFind11Rank
     UnionFind12RankEmptyCreate UnionFind13RankLink UnionFind14RankCompress
     UnionFind15RankJoin UnionFind41Potential UnionFind43PotentialAnalysis
     UnionFind44PotentialJoin.

(* Load the heap_lang code *)
From iris_time.union_find Require Import Code.

Section UnionFind.

Context `{!tctrHeapG Σ} (nmax : nat).

(* An object in the Union Find data structure is represented by an
   heap_lang location. *)
Notation elem := loc.

(* The logical type of the content of a vertex. *)
Inductive content :=
| Root : nat -> val -> content
| Link : elem -> content.

Definition val_of_content (c : content) : option val :=
  match c with
  | Root k v => (λ (k : mach_int), ROOTV(#k, v)) <$> to_mach_int k
  | Link e => Some $ LINKV #e
  end.

Lemma val_of_content_Some :
  forall c v,
    val_of_content c = Some v →
    (∃ (k1 : mach_int) (k2 : nat) v', v = ROOTV(#k1, v') /\ c = Root k2 v' /\ `k1 = k2)
    \/ (∃ e : elem, v = LINKV #e /\ c = Link e).
Proof.
  introv Hv. destruct c as [k2 v'|e]; [left|right].
  - simpl in Hv. destruct (to_mach_int k2) as [k1|] eqn:Hk12; [|done].
    eexists k1, k2, v'. repeat split; try naive_solver.
    unfold to_mach_int in Hk12. case_decide; inversion Hk12. done.
  - inversion Hv. eauto.
Qed.

Lemma val_of_content_Some_Root :
  forall k2 v v',
    val_of_content (Root k2 v') = Some v →
    (∃ (k1 : mach_int), v = ROOTV(#k1, v') /\ `k1 = k2).
Proof.
  introv [(? & ? & ? & -> & [= -> ->] & ?)|(? & ? & [=])]%val_of_content_Some. eauto.
Qed.

(* Hints for the type-checker. *)

(* It seems important that [D], [R], and [V] which are the public parameters to
   [UF], mention [elem] in their types, as opposed to [loc]. Internally [elem]
   is equal to [loc]. Ultimately, however, the type [elem] is made opaque. *)

Implicit Types x y r : elem.
Implicit Types v : val.
Implicit Types D : LibSet.set elem.  (* domain *)
Implicit Types F : binary elem.      (* edges *)
Implicit Types K : elem -> nat.      (* rank *)
Implicit Types R : elem -> elem.     (* functional view of [is_repr F] *)
Implicit Types V : elem -> val.      (* data stored at the roots *)
Implicit Types M : gmap elem content. (* view of the memory *)

(* -------------------------------------------------------------------------- *)

(* Invariants and representation predicate. *)

(* The predicate [Mem ...] relates the mathematical graph encoded by [D/F/K/V]
   and the memory encoded by the finite map [M]. In short,
    1. elements of [D] have a mapping in M;
    2. the links in [M] coincide with the links in [F];
    3. the rank and data stored at a root in [M] agree with [K] and [V]. *)

Definition Mem D F K V M : Prop :=
  forall x, x \in D ->
    match M!!x with
    | Some (Link y)   => F x y
    | Some (Root k v) => is_root F x /\ k = K x /\ v = V x
    | None => False
    end.

(* The predicate [Inv ...] relates the mathematical graph encoded by [D/F/K/V]
   and the view that is exposed to the client, which is encoded by [D/R/V].
   In short,
   1. [D/F/K] form a ranked disjoint set forest, as per [is_rdsf];
   2. [R] is included in [is_repr F],
      which means that [R x = y] implies [is_repr F x y],
      or in other words, [R] agrees with [F];
   3. [V] agrees with [R]. *)

Record Inv D F K R V : Prop := {
  Inv_rdsf  : is_rdsf D F K;
  Inv_incl  : fun_in_rel R (is_repr F);
  Inv_data  : forall x, V x = V (R x)
}.

Hint Resolve is_rdsf_is_dsf : core.
Hint Resolve Inv_rdsf Inv_incl Inv_data : core.

(* Throughout, we instantiate the parameter [r] of Alstrup et al.'s proof
   with the value 1. Thus, we write just [Phi] for [Phi 1]. *)

Notation Phi := (Phi 1).

(* [UF D R V] is the representation predicate. It is an abstract predicate: the
   client uses this predicate, but does not know how it is defined. *)

(* The definition asserts the existence (and ownership) of a group of references,
   whose content is described by a finite map [M]. It asserts the two invariants
   above. Finally, it asserts the existence (and ownership) of [Phi] time credits,
   which have been set aside to help pay for future operations. The definition
   quantifies existentially over [F/K/M], which therefore are not exposed to the
   client. *)

Definition mapsto_M M : iProp Σ :=
  ([∗ map] l ↦ c ∈ M, from_option (mapsto l (DfracOwn 1)) False (val_of_content c))%I.

Definition UF D R V : iProp Σ :=
  (∃ F K M,
  ⌜ Inv D F K R V ⌝ ∗
  ⌜ Mem D F K V M ⌝ ∗
  mapsto_M M ∗
  TC (11 * Phi D F K) ∗
  TR (card D))%I.

(* -------------------------------------------------------------------------- *)

(* The functions [V] and [R] are compatible with [R]. In other words, every
   member of an equivalence class must have the same image through [V] (see
   [Inv_data]) and through [R]. For this reason, when we wish to update one of
   these functions, we must update it not just at one point, but at a whole
   equivalence class. *)

(* The function [update1 R f x b] coincides with the function [f] everywhere,
   except on the equivalence class of [x], whose elements are mapped to [b]. *)

Definition update1 {B : Type} (f : elem -> B) R x (b : B) :=
  fcupdate f (fun z => R z = R x) b.

(* The function [update2 R f x y b] coincides with the function [f] everywhere,
   except on the equivalence classes of [x] and [y], whose elements are mapped
   to [b]. *)

Definition update2 {B : Type} (f : elem -> B) R x y b :=
  fcupdate f (fun z => R z = R x \/ R z = R y) b.

(* Updating [V] by mapping the equivalence classes of [x] and [x] to [V x]
   has no effect. *)

Lemma update2_V_self : forall D F K R V x,
  Inv D F K R V ->
  update2 V R x x (V x) = V.
Proof using.
  introv [ _ _ H ]. unfold update2.
  eapply fcupdate_self; intros.
  branches; rewrite H; congruence.
Qed.

(* If [x] is a root, then updating [R] by mapping the equivalence classes of [x]
   and [x] to [x] has no effect. *)

Lemma update2_R_self : forall R x,
  R x = x ->
  update2 R R x x x = R.
Proof using.
  intros. unfold update2.
  eapply fcupdate_self; intros.
  branches; congruence.
Qed.

(* Updating [f] at [R x] and [R y] is the same as updating [f] at [x] and [y]. *)

Lemma update2_root : forall (B : Type) (f : elem -> B) R x y b,
  idempotent R ->
  update2 f R (R x) (R y) b = update2 f R x y b.
Proof using.
  introv H. unfold update2. do 2 rewrite* H.
Qed.

(* Updating [V] at [x] and [y] is the same as updating [V] at [y] and [x]. *)

Lemma update2_sym : forall B (f : elem -> B) R x y b,
  update2 f R x y b = update2 f R y x b.
Proof using.
  intros. extens. intros z. unfold update2.
  f_equal. clear z. extens; intros z. tauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Exploitation and preservation lemmas for the invariant [Inv]. *)

(* If [x] is in the domain and [r] is its representative, then [r] is in the
   domain and [r] is its own representative. *)

Lemma Inv_root : forall D F K R V x r,
  Inv D F K R V ->
  x \in D ->
  r = R x ->
  r \in D /\ R r = r.
Proof using.
  intros; subst; split.
  applys* sticky_R.
  applys* idempotent_R.
Qed.

(* The invariant is preserved when a new element [r] is created and the
   function [V] is updated at [r] in an arbitrary manner. *)

Lemma Inv_make : forall D R F K V D' V' r v,
  Inv D F K R V ->
  r \notin D ->
  D' = D \u \{r} ->
  V' = update1 V R r v ->
  Inv D' F K R V'.
Proof using.
  introv HI Dr ED EV. subst D'. lets [Hrdsf Hroots Hdata]: HI.
  constructor.
  { eauto using is_rdsf_create. }
  { auto. }
  { subst V'. eapply fcupdate_absorbs; intros; eauto.
    rewrites* (>> idempotent_R R). }
Qed.

(* The invariant is preserved by updating [V] at one equivalence class. *)

Lemma Inv_update1 : forall D F K R V x v,
  Inv D F K R V ->
  Inv D F K R (update1 V R x v).
Proof using.
  introv [? ? ?]. constructors~; intros.
  eapply fcupdate_absorbs; intros; eauto.
  rewrites* (>> idempotent_R R).
Qed.

(* The invariant is preserved by a [link] operation. *)

(* The hypothesis is that the invariant holds and [x] and [y] are distinct roots
   in the domain. The conclusion is that the invariant holds again and the
   potential [Phi] grows by at most 2. The domain [D] is unchanged, while the
   other parameters [F'/K'/R'/V'/z] are described by five equations. *)

Lemma Inv_link: forall D R F K V F' K' V' x y z,
  (* Hypotheses: *)
  Inv D F K R V ->
  x ≠ y ->
  x \in D ->
  y \in D ->
  R x = x ->
  R y = y ->
  (* Five equations, describing the situation after the link: *)
  z = new_repr_by_rank K x y ->
  F' = link_by_rank_F F K x y ->
  K' = link_by_rank_K K x y ->
  V' = update2 V R x y (V z) ->
  let R' := link_by_rank_R R x y z in
  (* Conclusions: *)
  Inv D F' K' R' V' /\
  (Phi D F' K' <= Phi D F K + 2)%nat.
Proof.
  introv HI. intros. subst R' F' K' V' z. split. constructor.
  (* Preservation of [is_rdsf]. *)
  { eauto 8 using is_rdsf_link, R_self_is_root. }
  (* Preservation of the agreement between [R] and [F]. *)
  { eauto 8 using link_by_rank_R_link_by_rank_F_agree, R_self_is_root. }
  (* Preservation of the agreement between [V] and [R]. *)
  { intros w.
    unfold update2, fcupdate, link_by_rank_R. repeat case_if~.
    { false. forwards* HR: idempotent_R R. rewrite ->HR in *. tauto. }
    { rewrites~ <- (>> Inv_data HI). }
  }
  (* Change in potential. *)
  { eapply potential_increase_during_link; eauto using R_self_is_root. }
Qed.

(* This tactic helps apply the above lemma. The user is supposed to supply
   expressions for [F'/K'/V'/z], which we prove equal to what we expect.
   This allows some flexibility. *)

Ltac Inv_link F' K' V' x y z :=
  match goal with HInv: Inv ?D ?F ?K ?R ?V |- _ =>
    let Hpotential := fresh in
    (* Apply [Inv_link] to appropriate parameters. *)
    forwards* (?&Hpotential):
      (Inv_link _ _ _ _ _ F' K' V' x y z HInv);
    (* We expect to see some equations as sub-goals. We prove them by
       unfolding definitions and performing a simple case analysis. *)
    try solve [
       unfold new_repr_by_rank, link_by_rank_F, link_by_rank_K;
       case_if; solve [ eauto | math ]
     | congruence
    ]
  end.

(* -------------------------------------------------------------------------- *)

(* Exploitation and preservation lemmas for the invariant [Mem]. *)

(* If [x] is in the domain and is a root, then [M] maps [x] to [Root]
   with rank [K x] and data [V x]. *)

Lemma Mem_root : forall D R F K M V x,
  Inv D F K R V ->
  Mem D F K V M ->
  x \in D ->
  R x = x ->
  M!!x = Some (Root (K x) (V x)).
Proof using.
  introv HI HM Dx Rxx.
  forwards~ HV: HM x. destruct (M!!x) as [[]|]; [| |done].
    destruct HV as (?&?&?). congruence.
    false* (>> R_self_is_root HI HV).
Qed.

(* Conversely, if [M] maps [x] to [Root], then [x] is a root whose
   rank and data are as predicted by [M]. *)

Lemma Mem_root_inv : forall D F K M V x rx vx,
  Mem D F K V M ->
  x \in D ->
  M!!x = Some(Root rx vx) ->
  is_root F x /\ rx = K x /\ vx = V x.
Proof using.
  introv HM Dx HE. forwards~ HVx: HM x.
  destruct (M!!x) as [[]|]; [|false|done]. inverts* HE.
Qed.

(* [Mem] is preserved when a new element [r] is created with rank 0 and the
   function [V] is updated at [r] in an arbitrary manner. *)

Lemma Mem_make : forall D R F K D' r M V v,
  Inv D F K R V ->
  Mem D F K V M ->
  is_rdsf D F K ->
  r \notin D ->
  D' = D \u \{r} ->
  Mem D' F K (update1 V R r v) (<[r:=Root 0 v]>M).
Proof using.
  introv HI HV HG Dr -> Dx.
  rewrite in_union_eq in_single_eq in Dx. destruct Dx as [Dx| ->].
  { rewrite lookup_insert_ne; [|naive_solver].
    rewrite /update1 fcupdate_miss; [by apply HV|].
    intro. forwards* : R_is_identity_outside_D R r.
    forwards*: Inv_root x (R x). intuition congruence. }
  { rewrite lookup_insert /update1 fcupdate_hit //. splits.
    { eauto using only_roots_outside_D with is_dsf. }
    { (* We use the fact that [K] is zero outside the domain. *)
      erewrite is_rdsf_zero_rank_outside_domain; eauto. }
    { done. } }
Qed.

(* [Mem] is preserved by installing a link from a root [x] to a root [y]
   without updating any rank. *)

Lemma Mem_link : forall D F R K F' M V V' x y,
  Inv D F K R V ->
  Mem D F K V M ->
  x \in D ->
  x = R x ->
  y = R y ->
  F' = UnionFind03Link.link F x y ->
  V' = update2 V R x y (V y) ->
  Mem D F' K V' (<[x:=Link y]>M).
Proof using.
  introv HI HR Dx Rx Ry EG' HV. subst F'.
  intros a Da. specializes HR Da.
  destruct (decide (x = a)) as [->|].
  { rewrite lookup_insert. eauto using link_appears. }
  rewrite lookup_insert_ne //. destruct (M!!a) as [[]|]; [| |done]; first last.
  { eauto using link_previous. }
  rewrite~ HV. destruct HR as (?&?&E). splits*.
  { applys* is_root_link. }
  rewrites (rm E).
  unfold update2, fcupdate. rewrites <- (rm Rx). rewrites <- (rm Ry).
  forwards* Ra: is_root_R_self a. rewrite Ra. case_if~.
  branches. false. congruence.
Qed.

(* [Mem] is preserved by installing a link from a root [x] to a root [y]
   and incrementing the rank of [y]. *)

Lemma Mem_link_incr : forall D F R K F' K' M V V' x y (rx : nat) v,
  Inv D F K R V ->
  Mem D F K V M ->
  x \in D ->
  y \in D ->
  x = R x ->
  y = R y ->
  x ≠ y ->
  rx = K x ->
  F' = UnionFind03Link.link F x y ->
  K' = fupdate K y (1 + K x)%nat ->
  v = V y ->
  V' = update2 V R x y (V y) ->
  Mem D F' K' V' (<[y:=Root (rx + 1) v]>(<[x:=Link y]>M)).
Proof using.
  introv HI HM Dx Dy Rx Ry HN Hy Kx HK. introv Hv HV'.
  forwards* HV: (>> Mem_link V V' x y HM).
  sets M': (<[x := Link y]>M). clearbody M'.
  intros a Da. specializes HV Da. destruct (decide (y = a)) as [->|].
  { rewrite lookup_insert. splits.
    { subst F'. applys* is_root_link. applys* R_self_is_root. }
    { subst K'. subst rx. rewrite fupdate_same. math. }
    { subst v. subst V'. rewrite /update2 fcupdate_hit; by auto. } }
  rewrite lookup_insert_ne //. destruct (M'!!a) as [[]|]; [| |done].
  { subst F' K'. destruct HV. split~. unfolds fupdate. case_if~. }
  { subst F'. auto. }
Qed.

(* [Mem] is preserved by installing a direct link from [x] to [y] during
   path compression. *)

Lemma Mem_compress : forall D F K F' M V x y,
  Mem D F K V M ->
  x \in D ->
  F' = compress F x y ->
  Mem D F' K V (<[x:=Link y]>M).
Proof using.
  introv HR Dx EG'. subst.
  intros a Da. specializes HR Da. destruct (decide (x = a)) as [->|].
  { rewrite lookup_insert. eauto using compress_x_z. }
  { rewrite lookup_insert_ne //. destruct (M!!a) as [[]|];
      [|by eauto using compress_preserves_other_edges|done].
    destruct HR. split*.
    eauto using compress_preserves_roots_other_than_x. }
Qed.

(* [Mem] is preserved when [V] is updated at one equivalence class and [M]
   is updated at the representative element. *)

Lemma Mem_update1 : forall D R F K M V r x v,
  Inv D F K R V ->
  Mem D F K V M ->
  x \in D ->
  r = R x ->
  Mem D F K (update1 V R x v) (<[r := Root (K r) v]>M).
Proof using.
  introv HI HM E Rx. forwards* (Dr&Rr): Inv_root x r.
  intros y Dy. specializes HM Dy. destruct (decide (r = y)) as [->|].
  { rewrite lookup_insert. splits.
    { applys* R_self_is_root. }
    { done. }
    { rewrite /update1 fcupdate_hit; congruence. } }
  { rewrite lookup_insert_ne // /update1 /fcupdate. case_if~.
    destruct~ (M!!y) as [[]|]; [|done..]. destruct HM as (H1&H2&H3).
    forwards*: is_root_R_self H1. congruence. }
Qed.

(* -------------------------------------------------------------------------- *)

(* Private lemmas about the representation predicate and about [mapsto_M]. *)


Lemma mapsto_M_acc : forall M x c,
  M !! x = Some c ->
  mapsto_M M -∗
    ∃ v, ⌜val_of_content c = Some v⌝ ∗ x ↦ v ∗
     (∀ c' v', ⌜val_of_content c' = Some v'⌝ -∗
               x ↦ v' -∗ mapsto_M (<[x:=c']>M)).
Proof.
  introv HM. iIntros "HM".
  rewrite -[in mapsto_M M](insert_id M _ _ HM) -insert_delete_insert /mapsto_M.
  rewrite big_sepM_insert ?lookup_delete //. iDestruct "HM" as "[Hc HM]".
  destruct (val_of_content c); [|done]. iExists _. iFrame. iSplit; [done|].
  iIntros (c' v' Hv') "?".
  rewrite -insert_delete_insert big_sepM_insert ?lookup_delete // Hv'. iFrame.
Qed.

Lemma mapsto_M_acc_same : forall M x c,
  M !! x = Some c ->
  mapsto_M M -∗
    ∃ v, ⌜val_of_content c = Some v⌝ ∗ x ↦ v ∗ (x ↦ v -∗ mapsto_M M).
Proof.
  introv HM. iIntros "HM".
  iDestruct (mapsto_M_acc with "HM") as (v Hv) "[Hv HM]"; [done|].
  iExists _. iFrame. iSplit; [done|].
  iSpecialize ("HM" $! _ _ Hv). by rewrite insert_id.
Qed.

(* TODO : that should go into Iris libraries for big ops *)
Lemma mapsto_M_union : forall M1 M2,
  M1 ##ₘ M2 ->
  mapsto_M M1 ∗ mapsto_M M2 ⊣⊢ mapsto_M (M1 ∪ M2).
Proof.
  introv HM12. unfold mapsto_M.
  induction M1 as [|l x M1 ? IH] using map_ind.
  { by rewrite big_opM_empty !left_id. }
  rewrite -insert_union_l !big_sepM_insert //; last first.
  { apply lookup_union_None; split; [done|]. specialize (HM12 l).
    rewrite lookup_insert in HM12. revert HM12. case: (M2 !! l)=>//=. }
  rewrite -assoc. f_equiv. apply IH. by eapply map_disjoint_insert_l.
Qed.

Lemma mapsto_M_insert : forall M x c v,
  M !! x = None ->
  val_of_content c = Some v ->
  x ↦ v ∗ mapsto_M M ⊣⊢ mapsto_M (<[x:=c]>M).
Proof.
  introv Mxc Hcv. by rewrite /mapsto_M big_sepM_insert // Hcv.
Qed.

Lemma mapsto_M_disjoint : forall M1 M2,
  mapsto_M M1 -∗ mapsto_M M2 -∗ ⌜ M1 ##ₘ M2 ⌝.
Proof.
  iIntros "* HM1 HM2" (x). unfold mapsto_M.
  destruct (M1!!x) eqn:HM1, (M2!!x) eqn:HM2=>//.
  iDestruct (big_sepM_lookup with "HM1") as "H1"=>//.
  iDestruct (big_sepM_lookup with "HM2") as "H2"=>//.
  do 2 destruct val_of_content; try done.
  by iDestruct (mapsto_valid_2 with "H1 H2") as %[].
Qed.

(* -------------------------------------------------------------------------- *)

(* Public lemmas about the representation predicate. *)

(* If [UF D R V] holds, then [R] is idempotent. *)

Theorem UF_idempotent : forall D R V,
  UF D R V -∗ ⌜ idempotent R ⌝.
Proof using.
  iDestruct 1 as (?????) "?". eauto 10 using idempotent_R.
Qed.

(* If [UF D R V] holds, then [R] preserves [D]. *)

Theorem UF_image : forall D R V x, x \in D →
  UF D R V -∗ ⌜ R x \in D ⌝.
Proof using.
  iDestruct 1 as (?????) "?". eauto 10 using sticky_R.
Qed.

(* If [UF D R V] holds, then [R] is the identity outside of [D]. *)

Theorem UF_identity : forall D R V x, x \notin D ->
  UF D R V -∗ ⌜ R x = x ⌝.
Proof using.
  iDestruct 1 as (?????) "?". eauto 10 using R_is_identity_outside_D.
Qed.

(* If [UF D R V] holds, then [V] is compatible with [R]. *)

Theorem UF_compatible : forall D R V x, x \in D ->
  UF D R V -∗ ⌜ V x = V (R x) ⌝.
Proof using.
  iDestruct 1 as (?????) "?". eauto.
Qed.

(* An empty instance of the Union-Find data structure can be created out of
   thin air. This is how the data structure is initialized. *)

Theorem UF_create : forall V,
  TCTR_invariant nmax ={⊤}=∗ UF \{} id V.
Proof using.
  unfold UF. iIntros (V) "#?".
  iExists (@LibRelation.empty elem), (λ _, 0%nat), ∅.
  repeat iSplitL.
  { iPureIntro. constructors.
    { apply is_rdsf_empty. }
    { intro x. eapply is_repr_empty. }
    { eauto. } }
  { iIntros "!%" (??). false. }
  { rewrite /mapsto_M. by auto. }
  { rewrite Phi_empty. by iApply zero_TC. }
  { rewrite card_empty. by iApply zero_TR. }
Qed.

(* Two separate instances of the UnionFind data structure can be merged, without
   actually doing anything at runtime. *)

(* In principle, we could also prove the converse property, [UF_split]. A UnionFind
   data structure can be split in two independent parts, provided the split respects
   the equivalence relation. Considering the amount of dreary work that went into
   establishing [UF_join], I leave this to future work. *)

Theorem UF_join : forall D1 R1 V1 D2 R2 V2,
  UF D1 R1 V1 -∗ UF D2 R2 V2 -∗
  UF
    (D1 \u D2)
    (fun x => If x \in D1 then R1 x else R2 x)
    (fun x => If x \in D1 then V1 x else V2 x)
  ∗ ⌜ D1 \# D2 ⌝.
Proof using.
  intros.
  iDestruct 1 as (F1 K1 M1 HI1 HM1) "(HM1 & HTC1 & TR1)".
  iDestruct 1 as (F2 K2 M2 HI2 HM2) "(HM2 & HTC2 & TR2)".
  sets D: (D1 \u D2).
  sets R: (fun x => If x \in D1 then R1 x else R2 x).
  sets V: (fun x => If x \in D1 then V1 x else V2 x).
  set (F := LibRelation.union F1 F2).
  set (K := fun x => If x \in D1 then K1 x else K2 x).
  set (M := M1 ∪ M2).

  (* Disjointness lemmas. Trivial and painful. *)

  iDestruct (mapsto_M_disjoint with "HM1 HM2") as %HM12.

  assert (forall x, x \in D1 -> x \in D2 -> False).
  { intros l Hl1%HM1 Hl2%HM2. specialize (HM12 l).
    destruct (M1!!l) eqn:HM1l=>//. destruct (M2!!l) eqn:HM2l=>//. }

  assert (D1 \# D2) by by rew_set.

  assert (forall x, x \in D2 -> x \notin D1).
  { intros. intro. eauto. }

  assert (forall x y, F1 x y -> x \in D1).
  { eauto with confined is_dsf. }

  assert (forall x y, F2 x y -> x \in D2).
  { eauto with confined is_dsf. }

  assert (forall x, x \in D1 -> F1 x = F x).
  { intros. subst F. extens; intros y.
    unfold LibRelation.union; split; intros; try branches; eauto; false; eauto. }

  assert (forall x, x \in D2 -> F2 x = F x).
  { intros. subst F. extens; intros y.
    unfold LibRelation.union; split; intros; try branches; eauto; false; eauto. }

  assert (forall x, x \in D1 -> K1 x = K x).
  { intros. subst K. simpl. cases_if~. }

  assert (forall x, x \in D2 -> K2 x = K x).
  { intros. subst K. simpl. cases_if~. false; eauto. }

  assert (forall x, x \in D1 -> R1 x = R x).
  { intros. subst R. simpl. cases_if~. }

  assert (forall x, x \in D2 -> R2 x = R x).
  { intros. subst R. simpl. cases_if~. false; eauto. }

  assert (forall x, x \in D1 -> V1 x = V x).
  { intros. subst V. simpl. cases_if~. }

  assert (forall x, x \in D2 -> V2 x = V x).
  { intros. subst V. simpl. cases_if~. false; eauto. }

  assert (forall x, x \in D1 -> M1!!x = M!!x).
  { intros x Hx%HM1. subst M. destruct (M1!!x) eqn:? =>//.
    symmetry. by apply lookup_union_Some_l. }

  assert (forall x, x \in D2 -> M2!!x = M!!x).
  { intros x Hx%HM2. subst M. destruct (M2!!x) eqn:? =>//.
    symmetry. by apply lookup_union_Some_r. }

  iSplit; last done. iExists F, K, M.

  iCombine "HTC1 HTC2" as "HTC".
  iCombine "TR1 TR2" as "HTR".
  rewrite -mapsto_M_union // -Nat.mul_add_distr_l (@Phi_join 1 _ D F K); eauto.
  rewrite -card_disjoint_union; eauto using is_rdsf_finite; [].
  iFrame. iPureIntro. split.

  (* Preservation of [Inv]. *)
  { destruct HI1, HI2. constructor.
    (* Preservation of [is_rdsf]. *)
    { subst D F K. eapply is_rdsf_join; eauto. }
    (* Preservation of the agreement between [R] and [F]. *)
    { intros x. subst F R. simpl. cases_if.
      (* Case: [x \in D1]. *)
      { eapply is_repr_join_direct_1; eauto. }
      (* Case: [x \notin D1]. *)
      { eapply is_repr_join_direct_2; eauto. }
    }
    (* Preservation of the compatibility of [V]. *)
    { intros x. subst V R. simpl. cases_if; [ | destruct (classic (x \in D2)) ].
      (* Case: [x \in D1]. *)
      { assert (R1 x \in D1). { eauto using sticky_R. }
        cases_if. intuition eauto. }
      (* Case: [x \in D2]. *)
      { assert (R2 x \in D2). { eauto using sticky_R. }
        cases_if. false; eauto. eauto. }
      (* Case: [x \notin D1 \u D2]. *)
      { assert (h: R2 x = x). { eapply R_is_identity_outside_D; eauto with is_dsf. }
        rewrite h. cases_if. reflexivity. }
    }
  }

  (* Preservation of [Mem]. *)
  { intros x Dx. subst D. rewrite in_union_eq in Dx.
    destruct Dx as [ Dx | Dx ].
    { forwards : HM1 Dx. destruct (M1!!x) as [c|] eqn:EQM1=>//.
      unfold is_root in *. rewrite (lookup_union_Some_l _ _ _ _ EQM1) //.
      repeat match goal with h: forall_ x \in D1, _ |- _ =>
        specializes h Dx; try rewrite <- h
      end. done. }
    { forwards : HM2 Dx. destruct (M2!!x) as [c|] eqn:EQM2=>//.
      unfold is_root in *. rewrite (lookup_union_Some_r _ _ _ _ HM12 EQM2) //.
      repeat match goal with h: forall_ x \in D2, _ |- _ =>
        specializes h Dx; try rewrite <- h
      end. done. } }
Qed.

(* -------------------------------------------------------------------------- *)

(* Verification of [make]. *)

(* The function call [make v] requires [UF D R V] as well as O(1) time credits.
   It returns a new element [x], that is, [x] is not in [D]. It updates the
   data structure to [UF D' R' V'], where:
   1. [D'] is [D] extended with [x];
   2. [R'] is [R];
   3. [V'] is [V] extended with a mapping of [x] to [v]. *)

Theorem make_spec : forall D R V v,
  TCTR_invariant nmax -∗
  {{{ UF D R V ∗ TC 26 }}}
    «make v»
  {{{ (x : elem), RET #x;
      let D' := D \u \{x} in
      let V' := update1 V R x «v»%V in
      UF D' R V' ∗
      ⌜x \notin D /\
       R x = x⌝ }}}.
Proof using.
  iIntros "* #?" (Φ) "!# [HF TC] HΦ".
  wp_tick_rec. wp_tick_pair. wp_tick_inj.
  iMod zero_TR as "TR".
  wp_tick. wp_alloc x as "Hx". iApply "HΦ".
  iDestruct "HF" as (F K M HI HM) "(HM & TC' & TR')".

  iAssert ⌜M !! x = None⌝%I as %Mx.
  { case HMx: (M!!x)=>//.
    iDestruct (big_sepM_lookup with "HM") as "Hx'"=>//.
    destruct val_of_content; try done.
    by iDestruct (mapsto_valid_2 with "Hx Hx'") as %[]. }
  assert (x \notin D) as Dx.
  { intros Dx%HM. by rewrite Mx in Dx. }

  iSplit; [|by eauto 10 using R_is_identity_outside_D].
  iExists _, _, (<[x:=Root 0 _]>M).
  rewrite -Phi_extend 1?Nat.mul_add_distr_l; eauto; [].
  iCombine "TC' TC" as "$".

  rewrite card_disjoint_union; eauto using is_rdsf_finite, finite_single; last first.
  { by rewrite disjoint_single_r_eq. }
  rewrite card_single. iCombine "TR' TR" as "$".

  repeat iSplit; try iPureIntro.
  { applys* Inv_make. } { applys* Mem_make. }
  iApply mapsto_M_insert; [done| |by iFrame].
  rewrite /= /to_mach_int decide_True_pi /=; [by apply (proj2_sig mach_int_0)|].
  intros ?. by rewrite (exists_proj1_pi _ mach_int_0).
Qed.

(* -------------------------------------------------------------------------- *)

(* Verification of [find]. *)

(* Because [find] is a recursive function, we must begin with a specification
   that is amenable to an inductive proof. It states that [find] essentially
   implements the mathematical predicate [bw_ipc]. If [bw_ipc F x d F'] holds,
   which means that path compression at [x] requires [d] steps and changes the
   graph from [F] to [F'], then [find] requires [d+1] time credits and changes
   the memory from [M] to some [M'] that agrees with [F']. Furthermore, the
   value [r] returned by [find] is the representative of [x]. *)

Lemma find_spec_inductive: forall d D R F K F' M V x,
  Inv D F K R V ->
  Mem D F K V M ->
  x \in D ->
  bw_ipc F x d F' ->
  TCTR_invariant nmax -∗
  {{{ mapsto_M M ∗ TC (11*d+11) }}}
    «find #x»
  {{{ M', RET #(R x); mapsto_M M' ∗ ⌜ Mem D F' K V M' ⌝ }}}.
Proof using.
  intros d. induction_wf IH: Wf_nat.lt_wf d. intros d.
  introv IH HI HM Dx HC. iIntros "#?" (Φ) "!# [HM TC] HΦ /=".
  iDestruct "TC" as "[TCd TC]". wp_tick_rec.
  assert (HV := HM _ Dx). destruct (M !! x) as [c|] eqn:? =>//.
  iDestruct (mapsto_M_acc_same with "HM") as (v Hv) "[Hx HM]"=>//. wp_tick_load.
  iDestruct ("HM" with "Hx") as "HM".
  destruct (val_of_content_Some _ _ Hv) as [(k1 & k2 & v' & -> & -> & ?)|(y & -> & ->)].
  (* Case: Root. *)
  { wp_tick_match. wp_tick_proj. wp_tick_seq. wp_tick_proj. wp_tick_seq.
    destruct HV as [HR HP]. forwards* EQ : is_root_R_self HR. rewrite EQ.
    iApply "HΦ". iFrame. iPureIntro.
    invert HC; intros. by subst. by false* a_root_has_no_parent HR.
  }
  (* Case: Link. *)
  { wp_tick_match. rename HV into HF. invert HC.
    { intros. subst F. subst. false* a_root_has_no_parent. }
    intros F'0 F'' x0 y0 z' d' HF' HR' HB' EF' Ex Ed EF''. subst F'' x0 d.
    lets* E: is_dsf_functional D HF HF'. subst y0. clear HF'.
    assert (y \in D). { eauto with confined is_dsf. }
    assert (z' = R y). { symmetry. eapply is_repr_incl_R; eauto. } subst z'.
    forwards IH' : IH HI HM HB'; [math|done|].
    iCombine "TCd TC" as "TC".
    math_rewrite (11 * S d' + 6 = 11 * d' + 11 + 6)%nat ; first by lia.
    iDestruct "TC" as "[TCd TC]".
    wp_apply (IH' with "[//] [$HM $TCd]").
    iIntros (M') "[HM' hM']". iDestruct "hM'" as %HM'. wp_tick_let.
    assert (HV := HM' _ Dx). destruct (M' !! x) as [c|] eqn:? =>//.
    iDestruct (mapsto_M_acc with "HM'") as (v' Hv') "[Hx HM']"=>//.
    wp_tick_inj. wp_tick_store. wp_tick_seq.
    iDestruct ("HM'" $! (Link (R y)) _ eq_refl with "Hx") as "HM'".
    assert (is_equiv F x y). { eauto using path_is_equiv with rtclosure. }
    assert (R x = R y) as ->. { eauto using is_equiv_incl_same_R. }
    iApply ("HΦ" with "[$HM']").
    iPureIntro. applys~ Mem_compress HM'. }
Qed.

(* The function call [find x] requires [UF D R V] as well as O(alpha(D)) time
   credits. It preserves [UF D R V] and returns the representative of [x]. *)

Theorem find_spec : forall D R V x, x \in D ->
  TCTR_invariant nmax -∗
  {{{ UF D R V ∗ TC (22 * alpha (card D) + 44) }}}
    «find #x»
  {{{ RET #(R x); UF D R V }}}.
Proof using.
  introv Dx. iIntros "#?" (Φ) "!# [UF TC1] HΦ".
  iDestruct "UF" as (F K M HI HM) "(HM & TC2 & TR)".
  forwards* (d&F'&HC&HP): amortized_cost_of_iterated_path_compression_simplified x.
  iCombine "TC1 TC2" as "TC".
  rewrite [TC (_ + _)](TC_weaken _ (11*Phi D F' K + (11 * d + 11))%nat); [|lia].
  iDestruct "TC" as "[TC1 TC2]".
  iApply (find_spec_inductive with "[//] [$TC2 $HM]")=>//.
  iIntros "!>" (M') "[HM' %]". iApply "HΦ".
  iExists _, _, _. iFrame. iPureIntro. split; [|done].
  split; eauto 10 using is_rdsf_bw_ipc, bw_ipc_preserves_RF_agreement.
Qed.

(* -------------------------------------------------------------------------- *)

(* Verification of [get]. *)

(* The function call [get x] requires [UF D R V] as well as O(alpha(D)) time
   credits. It preserves [UF D R V] and returns the data stored at [x]. *)

Theorem get_spec : forall D R V x, x \in D ->
  TCTR_invariant nmax -∗
  {{{ UF D R V ∗ TC (22 * alpha (card D) + 57) }}}
    «get #x»
  {{{ RET V x; UF D R V }}}.
Proof using.
  introv Dx. iIntros "#?" (Φ) "!# [UF TC] HΦ".
  math_rewrite (22 * alpha (card D) + 57 = 22 * alpha (card D) + 44 + 13)%nat ;
    first by lia.
  iDestruct "TC" as "[TC1 TC2]".
  wp_tick_rec.
  wp_apply (find_spec with "[//] [$TC1 $UF]")=>//.
  iIntros "UF". wp_tick_let. iDestruct "UF" as (F K M HI HM) "[HM TC]".
  forwards* (Drx&Rrx): Inv_root x (R x).
  forwards* EM: Mem_root (R x).
  iDestruct (mapsto_M_acc_same with "HM") as (v Hv) "[Hx HM]"=>//. wp_tick_load.
  iDestruct ("HM" with "Hx") as "HM".
  destruct (val_of_content_Some_Root _ _ _ Hv) as (k1 & -> & _).
  wp_tick_match. wp_tick_proj. wp_tick_seq. wp_tick_proj. wp_tick_let.
  rewrite -(Inv_data _ _ _ _ _ HI). iApply "HΦ".
  iExists _, _, _. eauto with iFrame.
Qed.


(* -------------------------------------------------------------------------- *)

(* Verification of [set]. *)

(* The function call [set x v] requires [UF D R V] as well as O(alpha(D)) time
   credits. It produces [UF D R V'], where [V'] is obtained from [V] by mapping
   the equivalence class of [x] to [v]. *)

Theorem set_spec : forall D R V x v,
  x \in D ->
  TCTR_invariant nmax -∗
  {{{ UF D R V ∗ TC (22 * alpha (card D) + 62) }}}
    «set #x v»
  {{{ RET #(); UF D R (update1 V R x «v»%V) }}}.
Proof using.
  introv Dx. iIntros "#?" (Φ) "!# [UF TC] HΦ".
  math_rewrite (22 * alpha (card D) + 62 = 22 * alpha (card D) + 44 + 18)%nat ;
    first by lia.
  iDestruct "TC" as "[TC1 TC2]".
  wp_tick_rec. wp_tick_let. wp_apply (find_spec with "[//] [$TC1 $UF]")=>//.
  iIntros "UF". wp_tick_let. iDestruct "UF" as (F K M HI HM) "[HM TC]".
  forwards* (Drx&Rrx): Inv_root x (R x).
  forwards* EM: Mem_root (R x).
  iDestruct (mapsto_M_acc with "HM") as (v' Hv') "[Hx HM]"=>//. wp_tick_load.
  destruct (val_of_content_Some_Root _ _ _ Hv') as (k1 & -> & _).
  wp_tick_match. wp_tick_proj. wp_tick_seq. wp_tick_proj. wp_tick_seq.
  wp_tick_pair. wp_tick_inj. wp_tick_store.
  iApply "HΦ". iExists _, _, _. iFrame.
  iSplit; [auto using Inv_update1|]. iSplit; [eauto using Mem_update1|].
  rewrite Rrx. iApply ("HM" with "[%] Hx").
  simpl in *. by destruct (to_mach_int (K (R x))); inversion Hv'.
Qed.

(* -------------------------------------------------------------------------- *)

(* Verification of [eq]. *)

(* The function call [eq x y] requires [UF D R V] as well as O(alpha(D)) time
   credits. It preserves [UF D R V] and returns a Boolean outcome which
   indicates whether [x] and [y] are members of a common equivalence class. *)

Theorem eq_spec : forall D R V x y,
  x \in D -> y \in D ->
  TCTR_invariant nmax -∗
  {{{ UF D R V ∗ TC (44 * alpha (card D) + 92) }}}
    «eq #x #y»
  {{{ RET #(bool_decide (R x = R y)); UF D R V }}}.
Proof using.
  introv Dx Dy. iIntros "#?" (Φ) "!# [UF TC] HΦ".
  math_rewrite (44 * alpha (card D) + 92 =
                (22 * alpha (card D) + 44) + (22 * alpha (card D) + 44) + 4)%nat ;
    first by lia.
  iDestruct "TC" as "[[TC1 TC2] TC3]".
  wp_tick_rec. wp_tick_let.
  wp_apply (find_spec with "[//] [$TC1 $UF]")=>//. iIntros "UF".
  wp_apply (find_spec with "[//] [$TC2 $UF]")=>//. iIntros "UF".
  wp_tick_op.
  rewrite (bool_decide_iff (#(R x) = #(R y)) (R x = R y)); last (split; congruence).
  by iApply "HΦ".
Qed.

(* -------------------------------------------------------------------------- *)

(* Verification of [link]. (This is an internal function.) *)

(* The function call [link x y] requires [UF D R V] as well as O(1) time credits.
   It requires [x] and [y] to be roots. It chooses the new representative [z] to
   be one of [x] or [y], and returns [z], together with [UF D' R' V'], where:
   1. [D'] is [D], i.e., the domain is unchanged;
   2. [R'] is [R], where the equivalence classes of [x] and [y] are mapped to [z];
   3. [V'] is [V], where the equivalence classes of [x] and [y] are mapped to [V z].
*)

Lemma link_spec : forall D R V x y,
  (log2 (log2 nmax) < word_size - 1)%nat ->
  x \in D ->
  y \in D ->
  R x = x ->
  R y = y ->
  TCTR_invariant nmax -∗
  {{{ UF D R V ∗ TC 61 }}}
    «link #x #y»
  {{{ z, RET #z; UF D (update2 R R x y z) (update2 V R x y (V z)) ∗
                   ⌜z = x \/ z = y⌝}}}.
Proof using.
  introv Hnmax Dx Dy Rx Ry. iIntros "#?" (Φ) "!# [UF TC] HΦ".
  wp_tick_rec. wp_tick_let.
  iDestruct "UF" as (F K M HI HM) "(HM & TC'TR)".
  wp_tick_op. case_bool_decide as Hxy.
  (* Case: [x == y]. *)
  { inversion Hxy. subst. wp_tick_if. iApply "HΦ".
    rewrite update2_R_self; [|by eauto]. erewrite update2_V_self; [|by eauto..].
    iSplit; [|by auto]. iExists _, _, _. auto with iFrame. }
  (* Case: [x != y]. *)
  wp_tick_if.
  forwards Hx: HM Dx. forwards Hy: HM Dy.
  destruct (M !! x) as [cx|] eqn:EQx, (M !! y) as [cy|] eqn:EQy=>//.
  iDestruct (mapsto_M_acc_same _ x with "HM") as (v Hv) "[Hx HM]"=>//.
  wp_tick_load. iDestruct ("HM" with "Hx") as "HM".
  destruct cx; last by false; eauto using a_root_has_no_parent, R_self_is_root.
  destruct (val_of_content_Some_Root _ _ _ Hv) as (k1 & -> & ?).
  wp_tick_match. wp_tick_proj. wp_tick_let. wp_tick_proj. wp_tick_let.
  iDestruct (mapsto_M_acc_same _ y with "HM") as (v' Hv') "[Hy HM]"=>//.
  wp_tick_load. iDestruct ("HM" with "Hy") as "HM".
  destruct cy; last by false; eauto using a_root_has_no_parent, R_self_is_root.
  destruct (val_of_content_Some_Root _ _ _ Hv') as (k1' & -> & ?).
  wp_tick_match. wp_tick_proj. wp_tick_let. wp_tick_proj. wp_tick_seq.
  destruct Hx as (HRx&Kx&Vx). substs. destruct Hy as (HRy&Ky&Vy). substs.
  wp_tick_op; case_bool_decide; wp_tick_if;
    [|wp_tick_op; case_bool_decide; wp_tick_if].
  (* Sub-case: [K x < K y]. *)
  { iDestruct (mapsto_M_acc _ _ _ EQx with "HM") as (? _) "[Hx HM]".
    wp_tick_inj. wp_tick_store. wp_tick_seq. iApply "HΦ". iSplit; [|by auto].
    Inv_link
    (* F' := *) (UnionFind03Link.link F x y)
    (* K' := *) K
    (* V' := *) (update2 V R x y (V y))
                x y
    (* z  := *) y.
    iDestruct "TC'TR" as "[TC' TR]". iCombine "TC' TC" as "TC".
    iExists _, _, (<[x:=Link y]>M). iFrame "% TR".
    rewrite TC_weaken; [iFrame "TC"|lia]. iSplit; [by eauto using Mem_link|].
    by iApply "HM". }
  (* Sub-case: [K x > K y]. *)
  { iDestruct (mapsto_M_acc _ _ _ EQy with "HM") as (? _) "[Hy HM]".
    wp_tick_inj. wp_tick_store. wp_tick_seq. iApply "HΦ".
    rewrite [update2 _ _ _ _ x]update2_sym. rewrite [update2 _ _ _ _ (V x)]update2_sym.
    iSplit; [|by auto].
    Inv_link
    (* F' := *) (UnionFind03Link.link F y x)
    (* K' := *) K
    (* V' := *) (update2 V R y x (V x))
                y x
    (* z  := *) x.
    iDestruct "TC'TR" as "[TC' TR]". iCombine "TC' TC" as "TC".
    iExists _, _, (<[y:=Link x]>M). iFrame "% TR".
    rewrite TC_weaken; [iFrame "TC"|lia]. iSplit; [by eauto using Mem_link|].
    by iApply "HM". }
  (* Sub-case: [K x = K y]. *)
  { iDestruct (mapsto_M_acc _ _ _ EQy with "HM") as (? _) "[Hy HM]"=>//.
    wp_tick_inj. wp_tick_store.
    iDestruct ("HM" $! (Link _) _ eq_refl with "Hy") as "HM".
    Inv_link
    (* F' := *) (UnionFind03Link.link F y x)
    (* K' := *) (fupdate K x (1 + K y)%nat)
    (* V' := *) (update2 V R x y (V x))
                x y
    (* z  := *) x.
    iDestruct "TC'TR" as "[TC' TR]".
    iMod (TR_lt_nmax with "[//] TR") as "[TR %]" ; first done.
    iCombine "TC' TR" as "TC'TR".
    iAssert (⌜card D ≤ nmax⌝)%I%nat as %HDnmax%Nat.log2_le_mono.
    { auto with lia. }
    assert (bool_decide (mach_int_bounded (`k1 + 1))).
    { assert (log2 nmax < 2 ^ (word_size - 1))%nat.
      { destruct (decide (0 < log2 nmax)%nat); [by eapply Nat.log2_lt_pow2|].
        assert (log2 nmax = 0%nat) as -> by lia. apply power_positive. lia. }
      forwards* Hklog: rank_is_logarithmic (fupdate K x (S (K y))) x.
      rewrite fupdate_same in Hklog.
      assert (S (K y) < 2 ^ (word_size - 1))%nat as HK%inj_lt by lia.
      rewrite Z2Nat_inj_pow -Z.shiftl_1_l Nat2Z.inj_sub in HK;
        [|pose proof word_size_gt_1; lia].
      apply bool_decide_pack. split.
      { destruct (bool_decide_unpack _ (proj2_sig k1)) as [? _]. lia. }
      assert (`k1 = `k1') as -> by lia. rewrite (_:`k1' = K y) //.
      rewrite Z.add_comm -(Nat2Z.inj_add 1). done. }
    wp_tick_seq. wp_tick_op.
    { by rewrite /bin_op_eval /= /to_mach_int decide_True_pi. }
    iDestruct (mapsto_M_acc _ x with "HM") as (v'' Hv'') "[Hx HM]".
    { rewrite lookup_insert_ne //. congruence. }
    wp_tick_pair. wp_tick_inj. wp_tick_store. wp_tick_seq.
    iApply "HΦ". iSplit; [|by auto].
    iDestruct "TC'TR" as "[TC' TR]".
    iExists _, _, _. iFrame "% TR".
    iCombine "TC' TC" as "TC". rewrite TC_weaken; [iFrame "TC"|lia].
    iSplit; last iApply ("HM" with "[%] Hx").
    { iPureIntro. applys* Mem_link_incr HM. congruence. applys update2_sym. }
    rewrite /= -(_:(`k1 + 1) = (K y + 1)%nat) //.
    { by rewrite /to_mach_int decide_True_pi /=. }
    assert (`k1 + 1 = K y + 1)%Z as -> by lia. by rewrite ->Nat2Z.inj_add. }
Qed.

(* -------------------------------------------------------------------------- *)

(* Verification of [union]. *)

(* The function call [union x y] requires [UF D R V] as well as O(alpha(D)) time
   credits. It chooses the new representative [z] to be one of [x] or [y], and
   returns [z], together with [UF D' R' V'], where:
   1. [D'] is [D], i.e., the domain is unchanged;
   2. [R'] is [R], where the equivalence classes of [x] and [y] are mapped to [z];
   3. [V'] is [V], where the equivalence classes of [x] and [y] are mapped to [V z].
*)

Theorem union_spec : forall D R V x y,
  (log2 (log2 nmax) < word_size - 1)%nat ->
  x \in D ->
  y \in D ->
  TCTR_invariant nmax -∗
  {{{ UF D R V ∗ TC (44 * alpha (card D) + 152) }}}
    «union #x #y»
  {{{ z, RET #z; UF D (update2 R R x y z) (update2 V R x y (V z)) ∗
                 ⌜z = R x \/ z = R y⌝ }}}.
Proof using.
  introv Hnmax Dx Dy.
  math_rewrite (44 * alpha (card D) + 152 =
                (22 * alpha (card D) + 44) + (22 * alpha (card D) + 44) + 61 + 3)%nat ;
    first by lia.
  iIntros "#?" (Φ) "!# [UF [[[TC1 TC2] TC3] TC4]] HΦ".
  wp_tick_rec. wp_tick_let.
  wp_apply (find_spec with "[//] [$TC1 $UF]")=>//. iIntros "UF".
  wp_apply (find_spec with "[//] [$TC2 $UF]")=>//. iIntros "UF".
  iDestruct (UF_image _ _ _ x with "UF") as %? =>//.
  iDestruct (UF_image _ _ _ y with "UF") as %? =>//.
  iDestruct (UF_idempotent with "UF") as %Idem =>//.
  wp_apply (link_spec _ _ _ _ _ Hnmax with "[//] [$TC3 $UF]")=>//.
  iIntros (z). by rewrite !update2_root.
Qed.

End UnionFind.

Definition final_theorems :=
  (@UF_idempotent,
   @UF_image,
   @UF_identity,
   @UF_compatible,
   @UF_create,
   @UF_join,
   @make_spec,
   @find_spec,
   @get_spec,
   @set_spec,
   @eq_spec,
   @union_spec).
Print Assumptions final_theorems.
