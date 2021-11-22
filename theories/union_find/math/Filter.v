From TLC Require Import LibTactics.
From TLC Require Import LibLogic. (* defines [pred_incl] *)
From TLC Require Import LibSet.   (* defines [set] *)

(* ---------------------------------------------------------------------------- *)

(* Technically, a filter is a nonempty set of nonempty subsets of A, which is
   closed under inclusion and intersection. *)

Definition filter A := set (set A).

(* Intuitively, a filter is a modality. Let us write [ultimately] for a filter.
   If [P] is a predicate, then [ultimately P] is a proposition. Technically,
   this proposition asserts that [P] is an element of the filter; intuitively,
   it means that [P] holds ``in the limit''. *)

Class Filter {A : Type} (ultimately : filter A) := {

  (* A filter must be nonempty. *)
  filter_nonempty:
    exists P, ultimately P;

  (* A filter does not have the empty set as a member. *)
  filter_member_nonempty:
    forall P, ultimately P ->
    exists a, P a;

  (* A filter is closed by inclusion and by intersection. *)
  filter_closed_under_intersection:
    forall P1 P2 P : set A,
    ultimately P1 ->
    ultimately P2 ->
    (forall a, P1 a -> P2 a -> P a) ->
    ultimately P

}.

(* ---------------------------------------------------------------------------- *)

(* Basic properties of filters. *)

Section Properties.

  Context {A : Type} {ultimately : filter A} `{@Filter A ultimately}.

  (* A filter is closed by subset inclusion. In other words, if [ultimately]
     is a filter, then it is covariant. *)

  Lemma filter_closed_under_inclusion:
    forall P1 P2 : set A,
    ultimately P1 ->
    (forall a, P1 a -> P2 a) ->
    ultimately P2.
  Proof.
    intros. eapply filter_closed_under_intersection; eauto.
  Qed.

  (* A filter is compatible with extensional equality: if [P1] and [P2] are
     extensionally equal, then [ultimately P1] is equivalent to [ultimately
     P2]. *)

  Lemma filter_extensional:
    forall P1 P2 : set A,
    (forall a, P1 a <-> P2 a) ->
    (ultimately P1 <-> ultimately P2).
  Proof.
    introv h. split; intros; eapply filter_closed_under_inclusion; eauto;
    intros; eapply h; eauto.
  Qed.

  (* A filter always contains the universe as a member. In other words, if
     [P] holds everywhere, then [ultimately P] holds. *)

  Lemma filter_universe:
    forall P : set A,
    (forall a, P a) ->
    ultimately P.
  Proof.
    (* A filter is nonempty, so it has one inhabitant. *)
    destruct filter_nonempty.
    (* A filter is closed by inclusion, so the universe is also
       an inhabitant of the filter. *)
    eauto using @filter_closed_under_inclusion.
  Qed.

  (* If [P] holds ultimately and is independent of its argument, then [P]
     holds, period. *)

  Lemma filter_const:
    forall P : Prop,
    ultimately (fun _ => P) ->
    P.
  Proof.
    intros.
    forwards [ a ? ]: filter_member_nonempty. eauto.
    eauto.
  Qed.

End Properties.

(* ---------------------------------------------------------------------------- *)

(* Inclusion of filters. *)

Notation finer ultimately1 ultimately2 :=
  (pred_incl ultimately2 ultimately1).

Notation coarser ultimately1 ultimately2 :=
  (pred_incl ultimately1 ultimately2).

(* These relations are reflexive and transitive; see [pred_incl_refl] and
   [pred_incl_trans] in [LibLogic]. *)

(* ---------------------------------------------------------------------------- *)

(* Applying a function [f] to a filter [ultimately] produces another filter,
   known as the image of [ultimately] under [f]. *)

Definition image {A} (ultimately : filter A) {B} (f : A -> B) : set (set B) :=
  fun P => ultimately (fun x => P (f x)).

(* Make this a definition, not an instance, because we do not wish it to be
   used during the automated search for instances. *)

Definition filter_image {A} ultimately `{Filter A ultimately} {B} (f : A -> B) :
  Filter (image ultimately f).
Proof.
  econstructor; unfold image.
  (* There exists an element in this filter, namely the universe. *)
  exists (fun (_ : B) => True). eauto using filter_universe.
  (* No element of this filter is empty. *)
  intros.
  forwards [ a ? ]: filter_member_nonempty; eauto. simpl in *.
  eauto.
  (* This filter is stable under intersection. *)
  introv h1 h2 ?.
  eapply (filter_closed_under_intersection _ _ _ h1 h2).
  eauto.
Qed.

(* ---------------------------------------------------------------------------- *)

(* A notion of limit, or convergence. *)

(* The definition of [limit] does not really need proofs that [ultimatelyA]
   and [ultimatelyB] are filters. Requesting these proofs anyway is useful,
   as it helps the implicit argument inference system. *)

Definition limit
  {A} ultimatelyA `{Filter A ultimatelyA}
  {B} ultimatelyB `{Filter B ultimatelyB}
  (f : A -> B)
:=
  coarser ultimatelyB (image ultimatelyA f).

Lemma limit_id:
  forall A ultimately `{Filter A ultimately},
  limit _ _ (fun a : A => a).
Proof.
  unfold limit, image. repeat intro. eapply filter_closed_under_inclusion; eauto.
Qed.

(* ---------------------------------------------------------------------------- *)

(* The product of two filters. *)

Section FilterProduct.

Context {A1} ultimately1 `{Filter A1 ultimately1}.
Context {A2} ultimately2 `{Filter A2 ultimately2}.

Definition product : set (set (A1 * A2)) :=
  fun P : set (A1 * A2) =>
    exists P1 P2,
    ultimately1 P1 /\ ultimately2 P2 /\
    forall a1 a2, P1 a1 -> P2 a2 -> P (a1, a2).

Global Instance filter_product : Filter product.
Proof.
  econstructor; unfold product.
  (* Existence of a member. *)
  destruct (@filter_nonempty _ ultimately1) as [ P1 ? ]. eauto.
  destruct (@filter_nonempty _ ultimately2) as [ P2 ? ]. eauto.
  exists (fun a : A1 * A2 => let (a1, a2) := a in P1 a1 /\ P2 a2) P1 P2.
  eauto.
  (* Nonemptiness of the members. *)
  introv [ P1 [ P2 [ ? [ ? ? ]]]].
  forwards [ a1 ? ]: (filter_member_nonempty P1). eauto.
  forwards [ a2 ? ]: (filter_member_nonempty P2). eauto.
  exists (a1, a2). eauto.
  (* Closure under intersection and inclusion. *)
  intros P Q R.
  introv [ P1 [ P2 [ ? [ ? ? ]]]].
  introv [ Q1 [ Q2 [ ? [ ? ? ]]]].
  intros.
  exists (fun a1 => P1 a1 /\ Q1 a1).
  exists (fun a2 => P2 a2 /\ Q2 a2).
  repeat split.
  eapply filter_closed_under_intersection. 3: eauto. eauto. eauto.
  eapply filter_closed_under_intersection. 3: eauto. eauto. eauto.
  intuition eauto.
Qed.

(* When the pair [a1, a2] goes to infinity, its components go to infinity. *)

Lemma limit_fst:
  limit _ _ (@fst A1 A2).
Proof.
  unfold limit, image, product. simpl.
  intros P1 ?.
  exists P1 (fun _ : A2 => True).
  repeat split.
  eauto.
  eapply filter_universe. eauto.
  eauto.
Qed.

Lemma limit_snd:
  limit _ _ (@snd A1 A2).
Proof.
  unfold limit, image, product. simpl.
  intros P2 ?.
  exists (fun _ : A1 => True) P2.
  repeat split.
  eapply filter_universe. eauto.
  eauto.
  eauto.
Qed.

(* When both components go to infinity, the pair goes to infinity. *)

(* The limit of a pair is a pair of the limits. *)

Lemma limit_pair :
  forall A ultimately `{@Filter A ultimately},
  forall (f1 : A -> A1) (f2 : A -> A2),
  limit _ _ f1 ->
  limit _ _ f2 ->
  limit _ _ (fun a => (f1 a, f2 a)).
Proof.
  unfold limit, image.
  introv ? h1 h2. intros P [ P1 [ P2 [ ? [ ? ? ]]]].
  eapply filter_closed_under_intersection.
    eapply h1. eauto.
    eapply h2. eauto.
    eauto.
Qed.

End FilterProduct.

