Set Implicit Arguments.
From TLC Require Import LibTactics LibLogic LibProd LibEpsilon LibContainer
     LibSet LibRelation LibPer LibMonoid.
Local Notation path := rtclosure.
From iris_time.union_find.math Require Import LibNatExtra LibIter InverseNatNat
     LibRewrite LibFunOrd Ackermann InverseAckermann MiscArith TLCBuffer
     UnionFind01Data UnionFind11Rank UnionFind21Parent UnionFind41Potential.

Section Join.

Variable r : nat.

Notation rankr := (rankr r).
Notation prek := (prek r).
Notation k := (k r).
Notation i := (i r).
Notation phi := (phi r).
Notation Phi := (Phi r).

Variable V : Type.
Variable D : set V.
Variable F : binary V.
Variable K : V -> nat.

Section Inclusion.

(* In this section, we prove that if [D1/F1/K1] is a sub-forest of [D/F/K],
   then the potential of a node in [D1] with respect to [F1/K1] is the same
   as its potential with respect to [F/K]. The proof is uninteresting. *)

Variable D1 : set V.
Variable F1 : binary V.
Variable K1 : V -> nat.

Hypothesis FF:
  forall x,
  x \in D1 ->
  F1 x = F x.

Hypothesis KK:
  forall x,
  x \in D1 ->
  K1 x = K x.

Variable hrdsf1:
  is_rdsf D1 F1 K1. (* maybe overkill; confinement of [F1] in [D1] might suffice *)

Lemma rankr_eq:
  forall x,
  x \in D1 ->
  rankr K1 x = rankr K x.
Proof using KK.
  intros. unfold rankr. rewrite KK by eauto. reflexivity.
Qed.

Lemma p_eq:
  forall x,
  x \in D1 ->
  p F1 x = p F x.
Proof using FF.
  intros. unfold p, rel_to_fun', rel_to_fun. rewrite FF by eauto. reflexivity.
Qed.

Lemma prek_eq:
  forall x,
  x \in D1 ->
  ~ is_root F1 x ->
  prek F1 K1 x = prek F K x.
Proof using FF KK hrdsf1.
  intros. unfold prek, defk.
  rewrite rankr_eq by eauto.
  rewrite rankr_eq by eauto using parent_in_D.
  rewrite p_eq by eauto.
  reflexivity.
Qed.

Lemma k_eq:
  forall x,
  x \in D1 ->
  ~ is_root F1 x ->
  k F1 K1 x = k F K x.
Proof using FF KK hrdsf1.
  intros. unfold k. rewrite prek_eq by eauto. reflexivity.
Qed.

Lemma i_eq:
  forall x,
  x \in D1 ->
  ~ is_root F1 x ->
  i F1 K1 x = i F K x.
Proof.
  intros. unfold i.
  rewrite prek_eq by eauto.
  rewrite rankr_eq by eauto.
  rewrite rankr_eq by eauto using parent_in_D.
  rewrite p_eq by eauto.
  reflexivity.
Qed.

Lemma is_root_eq:
  forall x,
  x \in D1 ->
  is_root F1 x = is_root F x.
Proof using FF.
  intros. unfold is_root. rewrite FF by eauto. reflexivity.
Qed.

Lemma phi_eq:
  forall x,
  x \in D1 ->
  phi F1 K1 x = phi F K x.
Proof using FF KK hrdsf1.
  intros. unfold phi.
  rewrite is_root_eq by eauto.
  cases_if.
  { rewrite rankr_eq by eauto. reflexivity. }
  rewrite <- is_root_eq in * by eauto. (* needed by [parent_in_D] below *)
  rewrite rankr_eq by eauto.
  rewrite rankr_eq by eauto using parent_in_D.
  rewrite p_eq by eauto.
  cases_if; [ | reflexivity ].
  rewrite k_eq by eauto.
  rewrite i_eq by eauto.
  reflexivity.
Qed.

Lemma Phi_eq:
  Phi D1 F1 K1 = Phi D1 F K.
Proof using FF KK hrdsf1.
  intros. unfold Phi.
  eapply fold_congruence; eauto with finite typeclass_instances. intros x Dx.
  eauto using phi_eq.
Qed.

End Inclusion.

(* We conclude that if one joins two independent forests [D1/F1/K1] and [D2/F2/K2]
   then the potential of the new forest is the sum of the potentials of the original
   forests. *)

Lemma Phi_join:
  forall D1 F1 K1 D2 F2 K2,
  is_rdsf D1 F1 K1 ->
  is_rdsf D2 F2 K2 ->
  D1 \# D2 ->
  D = D1 \u D2 ->
  (forall x, x \in D1 -> F1 x = F x) ->
  (forall x, x \in D2 -> F2 x = F x) ->
  (forall x, x \in D1 -> K1 x = K x) ->
  (forall x, x \in D2 -> K2 x = K x) ->
  Phi D1 F1 K1 + Phi D2 F2 K2 = Phi D F K.
Proof using.
  intros. unfold Phi. subst D.
  rewrite fold_union; eauto with finite typeclass_instances.
  simpl. f_equal; eapply Phi_eq; eauto.
Qed.

End Join.

