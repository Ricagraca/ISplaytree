Set Implicit Arguments.
From TLC Require Import LibTactics LibLogic LibProd LibContainer LibSet
     LibRelation LibPer.
Local Notation path := rtclosure.
From iris_time.union_find.math Require Import TLCBuffer.

(* Definition of disjoint set forests. *)

Section DisjointSetForest.

(* -------------------------------------------------------------------------- *)

(* A type of vertices. *)

Variable V : Type.

(* We restrict our attention to a certain set of vertices, the domain
   of the forest. Keeping track of [D] allows us to distinguish an
   isolated vertex from a vertex that does not exist at all. *)

Variable D : set V.

(* The type [binary V] is the type of binary relations over [V].
   It is defined as [V -> V -> Prop]. This type can also be viewed
   as the type of directed graphs over vertices of type [V]. In the
   following, we define a disjoint set forest (dsf, for short) as a
   directed graph that satisfies certain properties. *)

Variable F : binary V.

(* A vertex [x] is a root if it has no successor. *)

Definition is_root x :=
  forall y, ~ F x y.

(* The descendants of [r] are the vertices [x] such that there exists
   a path from [x] to [r]. *)

Definition descendants r : set V :=
  \set{ x | path F x r }.

(* In a functional graph (i.e., a graph where every vertex has at most one
   successor), the vertex [r] is the representative for the vertex [x] iff
   there is a path from [x] to [r] and [r] is a root. In other words, there
   exists a maximal path from [x] to [r]. *)

Definition is_repr x r :=
  path F x r /\ is_root r.

(* A graph is a disjoint set forest with domain [D] iff every edge begins and
   ends within [D] and the graph is functional (i.e., every vertex has at most
   one successor) and acyclic (i.e., every vertex has a representative). *)

Definition is_dsf :=
  confined D F /\
  functional F /\
  defined is_repr.

(* Two vertices are equivalent if they have a common representative. *)

Definition is_equiv x y :=
  exists r, is_repr x r /\ is_repr y r.

(* The partial equivalence relation (PER) encoded by this disjoint set forest
   is the restriction of [is_equiv] to the domain [D]. *)

Definition dsf_per : binary V :=
  confine D is_equiv.

(* -------------------------------------------------------------------------- *)

(* In the following, we assume that [F] is a disjoint set forest with
   domain [D]. *)

Hypothesis is_dsf_F:
  is_dsf.

Definition is_dsf_confined := proj31 is_dsf_F.
Definition is_dsf_functional := proj32 is_dsf_F.
Definition is_dsf_defined_is_repr := proj33 is_dsf_F.

Hint Resolve is_dsf_confined : confined.

Hint Resolve is_dsf_functional : functional.

(* -------------------------------------------------------------------------- *)

(* Basic properties of [is_root], [is_repr], [is_equiv]. *)

(* A root has no parent. *)

Lemma a_root_has_no_parent:
  forall x y,
  is_root x ->
  F x y ->
  False.
Proof using.
  (* This is an immediate consequence of the definition. *)
  unfold is_root, not. intuition eauto.
Qed.

Lemma a_root_has_no_parent_disequality:
  forall r x y,
  is_root r ->
  F x y ->
  x <> r.
Proof using.
  intros. intro. subst. eauto using a_root_has_no_parent.
Qed.

Lemma a_root_has_no_parent_contrapositive:
  forall x y,
  F x y ->
  ~ is_root x.
Proof using.
  intros. unfold is_root. rewrite not_forall_not_eq. eauto.
Qed.

(* Hence, a path out of a root must be a trivial path. *)

Lemma a_path_out_of_a_root_is_trivial:
  forall x y,
  is_root x ->
  path F x y ->
  x = y.
Proof using.
  induction 2 using rtclosure_ind_l. eauto. false. eauto using a_root_has_no_parent.
Qed.

(* [is_repr x r] implies the existence of a path from [x] to [r]. *)

Lemma is_repr_path:
  forall x r,
  is_repr x r ->
  path F x r.
Proof using.
  unfold is_repr. tauto.
Qed.

(* The relation [is_repr] is functional, i.e., a vertex has at most
   one representative. *)

Lemma functional_is_repr:
  functional is_repr.
Proof using is_dsf_F.
  (* Massage the goal. *)
  unfold functional, is_repr.
  intros x r1 r2 [ ? ? ] [ ? ? ].
  generalize dependent r2. generalize dependent r1. generalize dependent x.
  (* Prove it. *) 
  induction 1 using rtclosure_ind_l; intros ? r2 [->|(?&?&?)]%rtclosure_inv_l ?;
    try solve [ false; eauto using a_root_has_no_parent ]; auto; [].
  exploit_functional F; eauto.
Qed.

Hint Resolve functional_is_repr : functional.

(* Two equivalent vertices must have the same representative. *)

Lemma is_repr_is_equiv_is_repr:
  forall x y r,
  is_repr x r ->
  is_equiv x y ->
  is_repr y r.
Proof using is_dsf_F.
  introv ? [ ? [ ? ? ]]. exploit_functional is_repr. eauto.
Qed.

Lemma is_repr_is_equiv_is_repr_bis:
  forall x y rx ry,
  is_repr x rx ->
  is_equiv x y ->
  is_repr y ry ->
  rx = ry.
Proof using is_dsf_F.
  introv ? [ ? [ ? ? ]] ?. do 2 exploit_functional is_repr. eauto.
Qed.

(* [is_equiv] is an equivalence relation. *)

Lemma is_equiv_refl:
  (* refl is_equiv *)
  forall x,
  is_equiv x x.
Proof using is_dsf_F.
  unfold is_equiv. intros x.
  forwards: is_dsf_defined_is_repr x.
  jauto.
Qed.

Lemma is_equiv_sym:
  (* sym is_equiv *)
  forall x y,
  is_equiv x y ->
  is_equiv y x.
Proof using.
  unfold is_equiv. intros x y (r & ? & ?). eauto.
Qed.

Lemma is_equiv_trans:
  (* trans is_equiv *)
  forall y x z,
  is_equiv x y ->
  is_equiv y z ->
  is_equiv x z.
Proof using is_dsf_F.
  unfold is_equiv.
  intros y x z (r1 & ? & ?) (r2 & ? & ?).
  exploit_functional is_repr. eauto.
Qed.

(* Two vertices that are connected by a path must be equivalent. *)

Lemma path_is_equiv:
  forall x y,
  path F x y ->
  is_equiv x y.
Proof using is_dsf_F.
  intros.
  forwards [ r ? ]: is_dsf_defined_is_repr y.
  assert (is_repr x r).
    { unfold is_repr in *. intuition eauto using rtclosure_trans_explicit. }
  exists r. eauto.
Qed.

(* [is_equiv] is the reflexive, symmetric, transitive closure of [F]. *)

Lemma is_equiv_rstclosure:
  is_equiv =
  rstclosure F.
Proof using is_dsf_F.
  extens. intros x y. split; intros.
  { unfold is_equiv, is_repr in *. unpack. 
    hint rstclosure_of_rtclosure.
    applys* trans_rstclosure r. { applys* sym_rstclosure. } }
  { gen x y. induction 1;
    eauto using path_is_equiv, is_equiv_refl, is_equiv_sym, is_equiv_trans with rtclosure. }
Qed.

(* A representative is a root. *)

Lemma is_repr_is_root:
  forall x r,
  is_repr x r ->
  is_root r.
Proof using.
  unfold is_repr. tauto.
Qed.

(* A root is its own representative. *)

Lemma is_root_is_repr:
  forall r,
  is_root r ->
  is_repr r r.
Proof using.
  unfold is_repr. eauto with rtclosure.
Qed.

(* A vertex is equivalent to its representative. *)

Lemma is_repr_equiv_root:
  forall x r,
  is_repr x r ->
  is_equiv x r.
Proof using.
  intros. exists r. eauto using is_repr_is_root, is_root_is_repr.
Qed.

(* [dsf_per] is indeed a partial equivalence relation. *)

Lemma per_dsf_per:
  per dsf_per.
Proof using is_dsf_F.
  unfold dsf_per, confine. constructor.
  intros x y. intuition eauto using is_equiv_sym.
  intros x y z. intuition eauto using is_equiv_trans.
Qed.

(* Its domain is indeed [D]. *)

Lemma per_dom_dsf_per:
  per_dom dsf_per = D.
Proof using is_dsf_F.
  unfold dsf_per, per_dom, confine. eapply set_ext.
  split; intros; rew_set in *; unpack; eauto using is_equiv_refl.
Qed.

(* There is a path from the parent [y] of a non-root vertex [x]
   to the representative [z] of [x]. *)

Lemma path_from_parent_to_repr_F:
  forall x y z,
  is_repr x z ->
  F x y ->
  path F y z.
Proof using is_dsf_F.
  intros.
  eapply is_repr_path.
  eapply is_repr_is_equiv_is_repr; eauto.
  eapply path_is_equiv; eauto with rtclosure.
Qed.

(* -------------------------------------------------------------------------- *)

(* Everything takes place within [D]. *)

Lemma sticky_path:
  sticky D (path F).
Proof using is_dsf_F.
  unfold sticky. induction 1 using rtclosure_ind_l; split; eauto 2 with confined.
    intros. eapply IHrtclosure. eauto with confined.
Qed.

Lemma sticky_is_repr:
  sticky D is_repr.
Proof using is_dsf_F.
  unfold sticky. intros. eapply sticky_path. eauto using is_repr_path.
Qed.

Lemma sticky_is_equiv:
  sticky D is_equiv.
Proof using is_dsf_F.
  unfold sticky. introv [ r [ ? ? ]].
  forwards: sticky_is_repr x r. eauto.
  forwards: sticky_is_repr y r. eauto.
  tauto.
Qed.

Hint Resolve sticky_path sticky_is_repr sticky_is_equiv : sticky.

Lemma is_equiv_in_D_direct:
  forall x y,
  is_equiv x y ->
  x \in D ->
  y \in D.
Proof using is_dsf_F.
  eauto with sticky.
Qed.

Lemma non_root_in_D:
  forall x,
  ~ is_root x ->
  x \in D.
Proof using is_dsf_F.
  unfold is_root. introv h. rewrite not_forall_not_eq in h. unpack. eauto with confined.
Qed.

Lemma only_roots_outside_D:
  forall x,
  x \notin D ->
  is_root x.
Proof using is_dsf_F.
  unfold notin. intros.
  destruct (classic (is_root x)).
  { assumption. }
  { forwards: non_root_in_D. eauto. tauto. }
Qed.

(* -------------------------------------------------------------------------- *)

(* If we are in a cycle and make one step, then we are still in a cycle. *)

Lemma one_step_in_a_cycle:
  forall x z,
  tclosure F x z ->
  x = z ->
  forall y,
  F x y ->
  tclosure F y y.
Proof using is_dsf_F.
  induction 1 using tclosure_ind_l; intros; subst; exploit_functional F.
  applys~ tclosure_once.
  eauto using tclosure_intro_right.
Qed.

(* Thus, a path cannot leave a cycle. *)

Lemma cannot_escape_a_cycle:
  forall x,
  tclosure F x x ->
  forall z,
  path F x z ->
  tclosure F z z.
Proof using is_dsf_F.
  induction 2; eauto using one_step_in_a_cycle.
Qed.

(* Thus, the fact every vertex has a representative contradicts the
   existence of a cycle. *)

Lemma acyclicity:
  forall x,
  tclosure F x x ->
  False.
Proof using is_dsf_F.
  intros.
  forwards [ z [ ? ? ]]: is_dsf_defined_is_repr x.
  forwards hz: cannot_escape_a_cycle; eauto.
  (* [z] is a root and a member of a cycle. Contradiction. *)
  destruct (tclosure_inv_l hz) as [|(?&?&?)];
    subst; eauto using a_root_has_no_parent.
Qed.

(* If there is a non-empty path from [x] to [y], then [x] and [y] must be distinct. *)

Lemma paths_have_distinct_endpoints:
  forall x y,
  tclosure F x y ->
  x <> y.
Proof using is_dsf_F.
  intros. intro. subst y. eauto using acyclicity.
Qed.

(* If there is an edge from [x] to [y], then [x] and [y] must be distinct. *)

Lemma edges_have_distinct_endpoints:
  forall x y,
  F x y ->
  x <> y.
Proof using is_dsf_F.
  eauto using paths_have_distinct_endpoints, tclosure_once with rtclosure.
Qed.

(* -------------------------------------------------------------------------- *)

(* Descendants. *)

(* [x] is a descendant of a root [r] iff [r] is the representative of [x]. *)

Lemma descendant_of_a_root:
  forall x r,
  is_root r ->
  (x \in descendants r <-> is_repr x r).
Proof using.
  clear is_dsf_F. (* prevent [set_prove] from using it. *)
  unfold descendants, is_repr. intros. set_prove.
Qed.

(* Two distinct roots have disjoint sets of descendants. *)

Lemma disjoint_descendants:
  forall x y,
  is_root x ->
  is_root y ->
  x <> y ->
  disjoint (descendants x) (descendants y).
Proof using is_dsf_F.
  intros. eapply prove_disjoint. intros v ? ?.
  rewrite descendant_of_a_root in * by eauto.
  exploit_functional is_repr. eauto.
Qed.

(* If [x] is in [D], then the set of its descendants is a subset of [D]. *)

Lemma descendants_subset_D:
  forall x,
  x \in D ->
  descendants x \c D.
Proof using is_dsf_F.
  unfold descendants. intros. eapply incl_prove. intros. rew_set in *. eauto with sticky.
Qed.

(* If a vertex [r] lies outside the domain, then a path that reaches [r]
   or leaves [r] must be trivial. *)

Lemma only_trivial_paths_outside_D:
  forall k x r,
  kpath F k x r ->
  x \notin D \/ r \notin D ->
  k = 0 /\ x = r.
Proof using is_dsf_F.
  induction 1 as [| y x r ]; intros.
  { eauto. }
  { false.
    assert (x \in D). { eauto with confined. }
    assert (y \in D). { eauto with confined. }
    assert (path F y r). { eauto using kpath_rtclosure. }
    assert (r \in D). { eauto with sticky. }
    unfold notin in *.
    tauto. }
Qed.

(* If a vertex [r] lies outside the domain, then its set of descendants is
   reduced to itself. *)

Lemma descendants_outside:
  forall r,
  r \notin D ->
  descendants r = \{r}.
Proof using is_dsf_F.
  unfold descendants. intros. eapply set_ext. split; intros; rew_set in *; subst.
  { forwards [ ? ? ]: rtclosure_kpath; eauto.
    forwards [ ? ? ]: only_trivial_paths_outside_D; eauto. }
  { eauto with rtclosure. }
Qed.

(* If [D] is finite, then every set of descendants is finite. *)

Lemma finite_descendants:
  forall x,
  finite D ->
  finite (descendants x).
Proof using is_dsf_F.
  intros.
  tests : (x \in D).
  { eauto using finite_incl, descendants_subset_D. }
  { rewrite descendants_outside by eauto.
    eauto with finite. }
Qed.

(* -------------------------------------------------------------------------- *)

(* Ancestors. *)

(* The ancestors of [x] are the vertices that lie along the path from [x]
   to its representative. *)

Definition ancestors x :=
  \set{ y | path F x y }.

(* If [x] is in [D], then the set of its ancestors is a subset of [D]. *)

Lemma ancestors_subset_D:
  forall x,
  x \in D ->
  ancestors x \c D.
Proof using is_dsf_F.
  unfold ancestors. intros. eapply incl_prove. intros. rew_set in *. eauto with sticky.
Qed.

(* If a vertex [r] lies outside the domain, then its set of ancestors is
   reduced to itself. *)

Lemma ancestors_outside:
  forall r,
  r \notin D ->
  ancestors r = \{r}.
Proof using is_dsf_F.
  unfold ancestors. intros. eapply set_ext. split; intros; rew_set in *; subst.
  { forwards [ ? ? ]: rtclosure_kpath; eauto.
    forwards [ ? ? ]: only_trivial_paths_outside_D; eauto. }
  { eauto with rtclosure. }
Qed.

(* If [D] is finite, then every set of ancestors is finite. *)

Lemma finite_ancestors:
  forall x,
  finite D ->
  finite (ancestors x).
Proof using is_dsf_F.
  intros.
  tests : (x \in D).
  { eauto using finite_incl, ancestors_subset_D. }
  { rewrite ancestors_outside by eauto.
    eauto with finite. }
Qed.

(* If there is an edge from [x] to [y], then the ancestors of [x] are the
   union of the ancestors of [y] and [x] itself. This is a disjoint union,
   because the graph is acyclic. *)

Lemma ancestors_of_parent_inclusion:
  forall x y,
  F x y ->
  ancestors y \c ancestors x.
Proof using is_dsf_F.
  unfold ancestors. intros. eapply incl_prove. intros; rew_set in *.
  eauto with rtclosure.
Qed.

Lemma ancestors_of_parent:
  forall x y,
  F x y ->
  ancestors x = ancestors y \u \{x}.
Proof using is_dsf_F.
  unfold ancestors. intros. eapply set_ext. split; intros; rew_set in *.
  (* An ancestor of [x] is either an ancestor of [y] or [x] itself. *)
  { match goal with h: path _ _ _ |- _ => destruct (rtclosure_inv_l h) as [|(?&?&?)] end;
    try exploit_functional F; eauto. }
  (* An ancestor of [y] is an ancestor of [x], and [x] is an ancestor of itself. *)
  { branches; subst; eauto with rtclosure. }
Qed.

Lemma ancestors_of_parent_disjoint:
  forall x y,
  F x y ->
  ~ x \in ancestors y.
Proof using is_dsf_F.
  unfold ancestors, notin. intros. rew_set in *.
  intro. eapply acyclicity. applys* tclosure_of_rtclosure_l.
Qed.

(* A root has no ancestors but itself. *)

Lemma ancestors_of_root:
  forall x,
  is_root x ->
  ancestors x = \{x}.
Proof using is_dsf_F.
  unfold ancestors. intros. eapply set_ext; split; rew_set in *.
  intros M. destruct (rtclosure_inv_l M) as [|(?&?&?)]; 
    subst; try solve [ eauto | false; eauto using a_root_has_no_parent ].
  intro; subst; eauto with rtclosure.
Qed.

(* There is at most one root ancestor. *)

Lemma at_most_one_root_ancestor:
  forall x y z,
  is_repr x z ->
  y \in ancestors x ->
  y <> z ->
  ~ is_root y.
Proof using is_dsf_F.
  unfold ancestors. intros; intro. rew_set in *; unpack.
  assert (is_repr x y). { econstructor; eauto. }
  exploit_functional is_repr. tauto.
Qed.

(* A hereditary property holds of every ancestor. *)

Lemma hereditary_property:
  forall (P : V -> Prop),
  (forall x y, P x -> F x y -> P y) ->
  forall x,
  P x ->
  forall y,
  y \in ancestors x ->
  P y.
Proof using.
  unfold ancestors.
  introv hh px yax.
  rew_set in *.
  induction yax; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* The relation [is_repr] is defined and functional, so it is the graph of a
   function [R] which maps every vertex to its representative. One may wish
   to present the end user with a specification expressed in terms of [R]. *)

(* We assume that the relation [R] is given and agrees with [is_repr]. If
   desired, the user can construct [R] explicitly as [choose_ is_repr]. *)

Variable R : V -> V.

(* The function [R] and the relation [is_repr] coincide. *)

Hypothesis R_incl_is_repr : fun_in_rel R is_repr.

Lemma is_repr_incl_R:
  rel_in_fun is_repr R.
Proof using is_dsf_F R_incl_is_repr.
  eauto using rel_in_fun_of_fun_in_rel_functional, functional_is_repr.
Qed.

(* [x] and [y] have the same image through [R] if and only if they are
   equivalent. In other words, the relation [is_equiv] coincides with
   the relation [fun x y => R x = R y]. *)

Lemma same_R_incl_is_equiv:
  forall x y,
  R x = R y ->
  is_equiv x y.
Proof using is_dsf_F R_incl_is_repr.
  introv h.
  forwards: R_incl_is_repr x.
  forwards: R_incl_is_repr y.
  rewrite <- h in *.
  unfold is_equiv. eauto.
Qed.

Lemma is_equiv_incl_same_R:
  forall x y,
  is_equiv x y ->
  R x = R y.
Proof using is_dsf_F R_incl_is_repr.
  unfold is_equiv. intros. unpack.
  forwards: is_repr_incl_R x. eauto.
  forwards: is_repr_incl_R y. eauto.
  congruence.
Qed.

(* [x] is a root if and only if [R x = x]. *)

Lemma is_root_R_self:
  forall x,
  is_root x ->
  R x = x.
Proof using is_dsf_F R_incl_is_repr.
  intros.
  forwards: is_root_is_repr. eauto.
  eapply functional_is_repr; eauto.
Qed.

Lemma R_self_is_root:
  forall x,
  R x = x ->
  is_root x.
Proof using R_incl_is_repr.
  introv h1.
  forwards h2: R_incl_is_repr x.
  rewrite h1 in h2.
  eauto using is_repr_is_root.
Qed.

(* [R] is the identity outside [D]. *)

Lemma R_is_identity_outside_D:
  forall x,
  x \notin D ->
  R x = x.
Proof using is_dsf_F R_incl_is_repr.
  intros. eapply is_root_R_self.
  eauto using only_roots_outside_D.
Qed.

(* [R] is idempotent. *)

Lemma idempotent_R:
  idempotent R.
Proof using is_dsf_F R_incl_is_repr.
  intro x.
  tests h : (x \in D).
  { eapply is_root_R_self.
    eapply is_repr_is_root.
    eapply R_incl_is_repr. }
  { forwards: R_is_identity_outside_D h.
    congruence. }
Qed.

(* [R] is sticky. *)

Lemma sticky_R:
  forall x,
  x \in D ->
  R x \in D.
Proof using is_dsf_F R_incl_is_repr.
  intros.
  forwards: R_incl_is_repr x.
  forwards: sticky_is_repr. eauto.
  tauto.
Qed.

(* -------------------------------------------------------------------------- *)

End DisjointSetForest.

Hint Resolve sticky_path sticky_is_repr sticky_is_equiv : sticky.

Hint Resolve is_dsf_functional functional_is_repr : functional.

Hint Resolve finite_descendants finite_ancestors : finite.

Hint Resolve is_repr_is_root : is_root.

Hint Resolve is_dsf_confined non_root_in_D : confined.

Hint Unfold is_repr : is_repr.

Hint Resolve is_repr_is_equiv_is_repr path_is_equiv : is_repr.

Hint Constructors rtclosure : is_repr.

Hint Unfold is_equiv : is_equiv.

Hint Resolve is_equiv_refl is_equiv_sym is_equiv_trans : is_equiv.

