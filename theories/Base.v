From Coq Require Export ssreflect.
From stdpp Require Export base list relations.

Tactic Notation "make_eq" constr(t) "as" ident(x) ident(E) :=
  set x := t ;
  assert (t = x) as E by reflexivity ;
  clearbody x.

Lemma take_cons {A : Type} (n : nat) (x : A) (xs : list A) :
  (0 < n)%nat → take n (x :: xs) = x :: take (n-1)%nat xs.
Proof.
  intros <- % Nat.succ_pred_pos. by rewrite /= - minus_n_O.
Qed.

Lemma drop_cons {A : Type} (n : nat) (x : A) (xs : list A) :
  (0 < n)%nat → drop n (x :: xs) = drop (n-1)%nat xs.
Proof.
  intros <- % Nat.succ_pred_pos. by rewrite /= - minus_n_O.
Qed.

Lemma nsteps_split `{R : relation A} m n x y :
  nsteps R (m+n) x y →
  ∃ (z : A), nsteps R m x z ∧ nsteps R n z y.
Proof.
  revert x ; induction m as [ | m' IH ] ; intros x H.
  - exists x. split ; [ constructor | assumption ].
  - inversion H as [ (*…*) | sum' x_ z y_ Hxz Hzy Esum' Ex Ey ] ; clear dependent sum' x_ y_.
    apply IH in Hzy as (ω & Hzω & Hωy).
    exists ω. split ; first econstructor ; eassumption.
Qed.
