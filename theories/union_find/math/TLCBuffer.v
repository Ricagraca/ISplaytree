Set Implicit Arguments.
From TLC Require Import LibTactics LibLogic LibEpsilon LibFun.
Require Import Coq.micromega.Lia.
Generalizable Variables A.

(* This file contains a bunch of stuff that needs to be (possibly cleaned up
   and) moved into TLC. *)

(* -------------------------------------------------------------------------- *)

(* This should move to LibFun. *)

(* The function [fcupdate f P b] coincides with the function [f] everywhere,
   except on the set [P], whose elements are mapped to [b]. *)

Definition fcupdate A B (f : A -> B) (P : A -> Prop) b :=
  fun a =>
    If P a then b else f a.

Lemma fcupdate_hit : forall A B (f : A -> B) (P : A -> Prop) b a,
  P a ->
  fcupdate f P b a = b.
Proof using.
  unfold fcupdate. intros. cases_if~.
Qed.

Lemma fcupdate_miss : forall A B (f : A -> B) (P : A -> Prop) b a,
  ~ P a ->
  fcupdate f P b a = f a.
Proof using.
  unfold fcupdate. intros. cases_if~.
Qed.

(* If every member of [P] is mapped by [f] to [b], then the updated function
   [fcupdate f P b] is just [f]. *)

Lemma fcupdate_self : forall A B (f : A -> B) (P : A -> Prop) b,
  (forall a, P a -> b = f a) ->
  fcupdate f P b = f.
Proof using.
  intros. unfold fcupdate. extens; intros. case_if~.
Qed.

(* Let [R] be a function of [A] to [A]. If [f] absorbs [R] and if [P] absorbs
   [R] then the updated function [fcupdate f P b] absorbs [R]. *)

Lemma fcupdate_absorbs : forall A B (f : A -> B) (P : A -> Prop) b (R : A -> A),
  (forall a, f a = f (R a)) ->
  (forall a, P a <-> P (R a)) ->
  (forall a, fcupdate f P b a = fcupdate f P b (R a)).
Proof using.
  introv ? HP. intros x. specializes HP x.
  unfold fcupdate. do 2 case_if~; false; tauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* LibTactics local extension. *)

Hint Extern 1 (_ = _) => congruence : congruence.

(* FRANCOIS: this should only be used for terminal goals *)
Ltac unpack := jauto_set_hyps; intros.

Ltac three_ways r1 r2 :=
  destruct (classicT (r1 = r2)); [ | destruct (classicT (r1 < r2)) ];
  repeat rewrite If_l in * by lia;
  repeat rewrite If_r in * by lia.

Ltac by_cases_on_fupdate :=
  rewrite fupdate_eq; case_if.

(* ------------------------------------------------------------------------- *)

(* LibRelation and LibPer *)

From TLC Require Import LibRelation LibPer.

(* The tactic [exploit_functional F] looks for two hypotheses of
   the form [F x y] and [F x z], where [F] is functional, and
   uses them to prove the equality [y = z] and simplify the goal. *)

Create HintDb functional.

Ltac exploit_functional F :=
  match goal with

  | h1: functional F, h2: F ?x ?y, h3: F ?x ?z |- _ =>
      assert (y = z); [
        solve [ eapply h1; eauto ]
      | clear h3; try subst y
      ]

  |                    h2: F ?x ?y, h3: F ?x ?z |- _ =>
      let f := fresh in
      assert (f: functional F); [
        solve [ eauto with functional ]
      | exploit_functional F; clear f
      ]

  end.

(* Some lemmas that prove membership in a relation. *)

Hint Resolve union_l union_r prove_per_single : relations.



(* A derived lemma involving a step from rtclosure to tclosure *)

Lemma tclosure_intro_right:
  forall (A : Type) (R : binary A) y x z,
  rtclosure R x y -> R y z -> tclosure R x z.
Proof using.
  Hint Constructors tclosure : core.
  introv M N. induction M using rtclosure_ind_l; autos*.
Qed.

(* An explicit formulation of [rtclosure_trans], which can be used by [eauto]. *)

Lemma rtclosure_trans_explicit:
  forall (A : Type) (R : binary A) y x z,
  rtclosure R x y -> rtclosure R y z -> rtclosure R x z.
Proof using. eapply rtclosure_trans. Qed.


(* ------------------------------------------------------------------------- *)

(* Path *)

(* TEMPORARY: the definition of kpath could be replaced with a predicate over a list *)

Section Closures.

Variables (A : Type) (R : binary A).

Inductive kpath : nat -> binary A :=
| KPathRefl:
    forall x,
    kpath 0 x x
| KPathStep:
    forall y x z k,
    R x y -> kpath k y z -> kpath (S k) x z.

Hint Constructors kpath : kpath.

Lemma kpath_rtclosure:
  forall k x y,
  kpath k x y ->
  rtclosure R x y.
Proof using.
  induction 1; eauto with rtclosure.
Qed.

Lemma rtclosure_kpath:
  forall x y,
  rtclosure R x y ->
  exists k, kpath k x y.
Proof using.
  introv M. induction M using rtclosure_ind_l;
  unpack; eauto with kpath.
Qed.

Lemma tclosure_kpath:
  forall x y,
  tclosure R x y ->
  exists k, kpath k x y /\ k > 0.
Proof using.
  introv M. induction M using tclosure_ind_l.
  { exists 1. eauto with kpath. }
  { destruct IHM as (k&?&?). exists (S k). split.
    constructors*. lia. }
Qed.

End Closures.

Hint Resolve kpath_rtclosure : rtclosure.


From TLC Require Import LibList.


(* ------------------------------------------------------------------------- *)


(* Intervals of the natural integers. *)
(* LATER: should be expressed on type fset *)
(* LATER: move to TLC, using TLC's comparison operator *)

Open Scope set_scope.
Require Import List.
From TLC Require Import LibList LibNat LibWf LibFix LibSet.
Close Scope comp_scope.

Definition interval_as_set (m n : nat) : set nat :=
  \set{ i | m <= i < n }.

Definition Interval_as_list f (m n:nat) :=
  If m >= n then nil else m::(f (S m) n).

Definition interval_as_list := FixFun2 Interval_as_list.

Lemma fix_interval_as_list : forall m n,
  interval_as_list m n = Interval_as_list interval_as_list m n.
Proof using.
  applys~ (FixFun2_fix (measure2 (fun m n => (n - m)%nat))).
  applys wf_measure2.
  introv IH. unfolds. case_if~. fequals.
  apply IH. simpls. nat_math.
Qed.

Lemma interval_as_list_length : forall m n, m <= n ->
  length (interval_as_list m n) = n - m.
Proof using.
  introv. induction_wf IH: (wf_nat_upto n) m. intros Le.
  rewrite fix_interval_as_list. unfold Interval_as_list.
  case_if; rew_list.
    nat_math.
    rewrite IH. nat_math. hnf. nat_math. nat_math.
Qed.

(* auxiliary lemma to help below *)
Lemma card_prove_eq' : forall A (E:set A) L n,
  list_covers E L ->
  length L = n ->
  (forall L', list_covers E L' -> (length L' >= n)%nat) ->
  card E = n.
Proof using.
  intros. subst. applys* list_covers_inv_card_eq.
Qed.

Lemma covers_interval_as_set:
  forall m n,
  list_covers (interval_as_set m n) (interval_as_list m n).
Proof using.
  unfold interval_as_set.
  introv Hx. rewrite in_set_st_eq in Hx. gen Hx.
  induction_wf IH: (wf_nat_upto n) m.
  introv L. rewrite fix_interval_as_list. unfold Interval_as_list.
  case_if.
    false. nat_math.
    tests: (x = m).
      auto.
      constructors. applys~ IH. unfolds. nat_math. nat_math.
Qed.

Lemma finite_interval_as_set:
  forall m n,
  finite (interval_as_set m n).
Proof using.
  intros. applys finite_of_list_covers (interval_as_list m n).
  applys covers_interval_as_set.
Qed.

Lemma card_interval_as_set:
  forall m n,
  m <= n ->
  card (interval_as_set m n) = n - m.
Proof using.
  intros. applys card_prove_eq'.
    applys covers_interval_as_set.
    applys~ interval_as_list_length.
  gen H. induction_wf IH: (wf_nat_upto n) m. introv H C.
  tests: (m = n). nat_math.
  forwards: IH (m+1) (filter (<> m) L').
    hnf; nat_math.
    nat_math.
    intros x Hx. unfolds interval_as_set. rewrite in_set_st_eq in Hx.
     forwards R: C x.
       rewrite in_set_st_eq. nat_math.
       applys~ mem_filter. nat_math.
  lets: filter_length_partition (=m) L'.
  forwards: length_filter_eq_mem_ge_one m L'.
    applys C. unfold interval_as_set. rewrite in_set_st_eq. nat_math.
  nat_math.
Qed.



(* -------------------------------------------------------------------------- *)

Lemma le_refl : refl Peano.le.
Proof using. intros_all; lia. Qed.
Hint Resolve le_refl : core.



(* -------------------------------------------------------------------------- *)


From TLC Require Import LibMin LibOrder.


(* Tactics for mmin *)

Ltac mmin_spec t :=
  let h1 := fresh "existence" in
  let h2 := fresh "minimality" in
  (forwards [ h1 h2 ]: @mmin_spec t); [
    try reflexivity
  |
  | eauto with admits_lower_bound
  | eauto with bounded_has_minimal
  | eauto 2 ].


(* For this development, we use a definition of [mmax] and [Mmax]
   provaby equivalent to the one in TLC's library. *)

Definition mmax `{Inhab A} (le:binary A) (P:A->Prop) :=
  mmin (inverse le) P.

Lemma mmax_equiv : @mmax = @LibMin.mmax.
Proof using.
  extens. intros. unfold mmax. rewrite~ <- mmax_inverse.
Qed.

Definition MMax `{Inhab A} `{Le A} := mmax le.



(* ------------------------------------------------------------------------- *)
(* Extension to LibSet *)

From TLC Require Import LibSet.

Section Autorewrite.
Variables (A : Type).
Implicit Types x y : A.
Implicit Types E F : set A.

Lemma notin_eq' : forall x E, (x \notin E) = ~ (x \in E).
Proof using. intros. apply notin_eq. Qed.

End Autorewrite.

Hint Rewrite notin_eq' : set_norm.


(* ------------------------------------------------------------------------- *)


(* LibContainer or LibSet *)

From TLC  Require Import LibMonoid LibSet.
Require Export Coq.Classes.Morphisms. (* for rewriting *)


(* In my opinion, \notin should be just a notation! *)

Lemma notin_eq :
  forall A (E : set A) x,
  (x \notin E) = (~ x \in E).
Proof using. intros. rewrite notin_eq. auto. Qed.

Lemma disjoint_single_left_eq:
  forall A (E : set A) x,
  \{x} \# E = ~ x \in E.
Proof using. intros. apply disjoint_single_l_eq. Qed.

Lemma disjoint_single_right_eq:
  forall A (E : set A) x,
  E \# \{x} = ~ x \in E.
Proof using. intros. apply disjoint_single_r_eq. Qed.

Lemma subset_single_eq:
  forall A (E : set A) x,
  \{x} \c E = x \in E.
Proof using. intros. apply single_incl_r_eq. Qed.

Lemma inter_union_disjoint_right:
  forall A (E F G : set A),
  F \# G ->
  (E \u F) \n G = (E \n G).
Proof using. set_prove. Qed.

Lemma inter_union_subset_right:
  forall A (E F G : set A),
  F \c G ->
  (E \u F) \n G = (E \n G) \u F.
Proof using. set_prove. Qed.

(* TEMPORARY should set up [Proper] instances for rewriting *)
Lemma inter_covariant:
  forall A (E E' F F' : set A),
  E \c E' ->
  F \c F' ->
  (E \n F) \c (E' \n F').
Proof using. set_prove. Qed.

(* Disjointness. *)

(* FRANCOIS : inline, except if used for automation *)
(* ARTHUR : look at the lemma [disjoint_descendants] in UnionFind01Data.v.
   [set_prove] alone cannot work
   [set_prove_setup false] seems to lose information; bug?
*)
Lemma prove_disjoint :
  forall (A : Type) (E F : set A),
  (forall x, x \in E -> x \in F -> False) ->
  E \# F.
Proof using. set_prove. Qed.
  (* TODO: add support for this: intros. applys Disjoint_prove. *)

(* ------------------------------------------------------------------------- *)


Hint Rewrite disjoint_single_left_eq disjoint_single_right_eq subset_single_eq
@notin_eq @in_empty_eq @in_single_eq @in_union_eq @in_inter_eq @in_remove_eq : rew_set.

Tactic Notation "rew_set" "in" "*" :=
  autorewrite with rew_set in *;
  eauto with typeclass_instances.

(* ------------------------------------------------------------------------- *)

Program Instance Reflexive_incl A :
  Reflexive (@LibContainer.incl _ (incl_inst A)).
Next Obligation.
  eapply incl_refl; eauto.
Qed.

Program Instance Transitive_incl A :
  Transitive (@LibContainer.incl _ (incl_inst A)).
Next Obligation.
  eapply incl_trans; eauto. typeclass.
Qed.

Program Instance Proper_inter_incl (A : Type) :
  Proper (@LibContainer.incl _ (incl_inst A) ++>
          @LibContainer.incl _ (incl_inst A) ++>
          @LibContainer.incl _ (incl_inst A))
  (@LibContainer.inter _ (inter_inst A)).
Next Obligation.
  repeat intro. eauto using inter_covariant.
Qed.

Goal
  forall A (E F G H : set A),
  E \c F ->
  F \n G \c H ->
  E \n G \c H.
Proof using.
  introv h1 h2.
  rewrite h1. rewrite h2. reflexivity.
Qed.

(* TEMPORARY DEPRECATED
Tactic Notation "set_in" :=
  match goal with
  | h: _ \in \{} |- _    => set_in h
  | h: _ \in \{_} |- _   => set_in h
  | h: _ \in _ \u _ |- _ => set_in h
  end.
*)


(* ------------------------------------------------------------------------- *)

Global  Instance monoid_plus_zero:
  Monoid (monoid_make plus 0).
Proof using.
  constructor; repeat intro; lia.
Qed.


Global Instance monoid_commutative_plus_zero:
  Comm_monoid (monoid_make plus 0).
Proof using.
  constructor. typeclass. intros_all; lia.
Qed.

(* ------------------------------------------------------------------------- *)

(* [confined D F] could be alternatively defined as:
   [confined D F := dom F = D /\ img F = D].
   where TLC would include
   [dom F = { x | exists y, F x y }]
   [img F = { y | exists x, F x y }].
  *)

(* A relation [F] is confined in a domain [D] iff [F x y]
   implies [x \in D] and [y \in D]. In other words, [F] is
   a subset of [D^2]. *)

Definition confined (A : Type) (D : set A) (F : binary A) :=
  forall x y, F x y -> x \in D /\ y \in D.

Lemma use_confined_left:
  forall (A : Type) (D : set A) F,
  confined D F ->
  forall x y,
  F x y ->
  x \in D.
Proof using.
  unfold confined. introv h. intros.
  forwards: h. eauto. tauto.
Qed.

Lemma use_confined_right:
  forall (A : Type) (D : set A) F,
  confined D F ->
  forall x y,
  F x y ->
  y \in D.
Proof using.
  unfold confined. introv h. intros.
  forwards: h. eauto. tauto.
Qed.

Lemma confined_contravariant:
  forall A (D1 D2 : set A) (F : binary A),
  confined D1 F ->
  D1 \c D2 ->
  confined D2 F.
Proof.
  unfold confined. introv Hc Hi. intros x y Hf.
  specializes Hc Hf. intuition eauto using @incl_inv with typeclass_instances.
Qed.

Lemma confined_union:
  forall (A : Type) D (F1 F2 : binary A),
  confined D F1 ->
  confined D F2 ->
  confined D (LibRelation.union F1 F2).
Proof using.
  unfold confined, LibRelation.union.
  intros. branches; eauto.
Qed.

Lemma confined_per_single:
  forall (A : Type) D (x y : A),
  x \in D ->
  y \in D ->
  confined D (per_single x y).
Proof using.
  unfold confined, per_single. intros; unpack; subst. eauto.
Qed.

Lemma confined_stclosure:
  forall (A : Type) D (F : binary A),
  confined D F ->
  confined D (stclosure F).
Proof using.
  unfold confined. introv h. induction 1; unpack; eauto.
Qed.

Lemma confined_disjoint_contradiction:
  forall A (D1 D2 : set A) (F1 F2 : binary A) x y z,
  confined D1 F1 ->
  confined D2 F2 ->
  D1 \# D2 ->
  F1 x y ->
  F2 x z ->
  False.
Proof.
  intros.
  assert (x \in D1). { eauto using use_confined_left. }
  assert (x \in D2). { eauto using use_confined_left. }
  rew_set in *.
Qed.

Hint Resolve use_confined_left use_confined_right confined_union
confined_per_single confined_stclosure : confined.

Definition confine (A : Type) (D : set A) (F : binary A) : binary A :=
  fun x y => x \in D /\ y \in D /\ F x y.

Ltac binary_extensional :=
  intros; unfold LibRelation.empty;
  eapply pred_ext_2;
  split; intros; unpack; rew_set in *; (* dependency on LibSet, not great *)
    try solve [ tauto | false ].

(* Confining a relation [F] to the empty set yields the empty relation. *)

Lemma confine_empty:
  forall A (F : binary A),
  confine \{} F = (@LibRelation.empty _).
Proof using.
  unfold confine. binary_extensional.
Qed.

Lemma confine_equiv_per:
  forall (A : Type) (F : binary A) (D : set A),
  equiv F ->
  per (confine D F).
Proof using.
  unfold confine. inversion 1.
  constructor; repeat intro; intuition eauto.
Qed.

Lemma confine_union_left:
  forall (A : Type) (D : set A) R S,
  confined D S ->
  LibRelation.union (confine D R) S =
  confine D (LibRelation.union R S).
Proof using.
  (* Slightly ad hoc statement and proof. *)
  unfold confined, confine, LibRelation.union.
  introv hc. eapply pred_ext_2; split; intros.
  { branches; unpack.
      eauto.
      forwards: hc. eauto. unpack. eauto. }
  { unpack. branches; eauto. }
Qed.

(* By construction, [confine D F] is confined within [D]. *)

Lemma confined_confine:
  forall (A : Type) (F : binary A) (D : set A),
  confined D (confine D F).
Proof using.
  unfold confined, confine. tauto.
Qed.

Lemma incl_confine:
  forall (A : Type) (F : binary A) (D : set A),
  rel_incl (confine D F) F.
Proof using.
  unfold rel_incl, confine. intuition eauto.
Qed.

Hint Resolve confined_confine incl_confine : confined.


(* ------------------------------------------------------------------------- *)

(** *

   [sticky D R] could be renamed as [is_component D R],
   in the graph terminology

*)

Definition sticky (A : Type) (D : set A) (R : binary A) :=
  forall x y, R x y -> (x \in D <-> y \in D).

Lemma use_sticky_left:
  forall (A : Type) (D : set A) (R : binary A) x y,
  x \in D ->
  R x y ->
  sticky D R ->
  y \in D.
Proof using.
  unfold sticky. introv ? ? h.
  forwards: h. eauto. tauto.
Qed.

Lemma use_sticky_right:
  forall (A : Type) (D : set A) (R : binary A) x y,
  y \in D ->
  R x y ->
  sticky D R ->
  x \in D.
Proof using.
  unfold sticky. introv ? ? h.
  forwards: h. eauto. tauto.
Qed.

Hint Resolve use_sticky_left use_sticky_right : sticky.

Lemma sticky_per_single:
  forall (A : Type) (D : set A) x y,
  (x \in D <-> y \in D) ->
  sticky D (per_single x y).
Proof using.
  unfold sticky, per_single.
  intros. unpack. subst. eauto.
Qed.

Lemma sticky_union:
  forall (A : Type) (D : set A) (R S : binary A),
  sticky D R ->
  sticky D S ->
  sticky D (LibRelation.union R S).
Proof using.
  unfold sticky, LibRelation.union.
  intros. branches; eauto.
Qed.

Lemma sticky_stclosure:
  forall (A : Type) (D : set A) (R : binary A),
  sticky D R ->
  sticky D (stclosure R).
Proof using.
  unfold sticky. induction 2. eauto. tauto. tauto.
Qed.

Hint Resolve sticky_per_single sticky_union sticky_stclosure : sticky.

Lemma confine_stclosure:
  forall (A : Type) (D : set A) (R : binary A),
  sticky D R ->
  confine D (stclosure R) = stclosure (confine D R).
Proof using.
  intros.
  assert (forall x y, stclosure R x y -> x \in D -> y \in D).
    { intros. forwards h: sticky_stclosure x y; eauto. tauto. }
  eapply pred_ext_2. split.
  (* One direction. *)
  { unfold confine. introv (? & ? & h). gen h. induction 1.
      { eapply stclosure_once. eauto. }
      { eapply stclosure_sym; eauto. }
      { eapply stclosure_trans; eauto. }
  }
  (* The other direction. *)
  { intros. repeat split; eauto with confined.
    applys covariant_stclosure H1.
    eauto with confined. }
Qed.



(* ------------------------------------------------------------------------- *)

(* TEMPORARY: comment *)

Lemma fold_pointwise :
  forall B (m : monoid_op B) (leB : B -> B -> Prop),
  Monoid m ->
  refl leB ->
  Proper (leB ++> leB ++> leB) (monoid_oper m) ->
  forall A (E : set A),
  finite E ->
  forall (f f' : A -> B),
  (forall x, x \in E -> leB (f x) (f' x)) ->
  leB (fold m f E) (fold m f' E).
Proof using.
  intros. do 2 rewrite fold_eq_fold_to_list.
  applys~ LibList.fold_pointwise.
  intros x. forwards~ (_&EQ): list_repr_to_list_of_finite E. rewrite (EQ x). auto.
Qed.

(* ------------------------------------------------------------------------- *)

Hint Resolve tclosure_of_rtclosure_r : tclosure.
