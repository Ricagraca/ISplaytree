Set Implicit Arguments.
Require Import Coq.micromega.Lia.
From iris_time.union_find.math Require Import LibFunOrd.

Section Iter.

Variable A : Type.

(* This iteration function is defined in [Coq.funind.Recdef].
   We repeat its definition here so as to be self-contained. *)

Fixpoint iter (n : nat) (f : A -> A) (x : A) :=
  match n with
  | O => x
  | S n => f (iter n f x)
  end.

(* Addition distributes onto [iter]. *)

Lemma iter_iter:
  forall f m n x,
  iter (m + n) f x = iter m f (iter n f x).
Proof using.
  induction m; simpl; intros; f_equal; auto.
Qed.

Lemma iter_iter_1p:
  forall f n x,
  iter (1 + n) f x = iter n f (f x).
Proof using.
  intros.
  replace (1 + n) with (n + 1) by lia.
  rewrite iter_iter.
  reflexivity.
Qed.

Lemma iter_iter_1:
  forall f n x,
  f (iter n f x) = iter n f (f x).
Proof using.
  intros.
  replace (f (iter n f x)) with (iter (1 + n) f x) by reflexivity.
  eapply iter_iter_1p.
Qed.

(* [iter] preserves [preserves okA]. *)

Variable okA : A -> Prop.

Lemma iter_preserves:
  forall f,
  preserves okA f ->
  forall n,
  preserves okA (iter n f).
Proof using.
  unfold preserves, within. induction n; simpl; auto.
Qed.

Lemma iter_invariant:
  forall n f x,
  okA x ->
  preserves okA f ->
  okA (iter n f x).
Proof using.
  intros. eapply iter_preserves; eauto.
Qed.

Lemma iter_indexed_invariant:
  forall (I : nat -> A -> Prop) f,
  (forall n x, I n x -> I (1 + n) (f x)) ->
  forall n x,
  I 0 x ->
  I n (iter n f x).
Proof using.
  induction n; simpl; eauto.
Qed.

(* [iter] preserves [monotonic leA leA]. Thus, if [f] is monotonic, then
   [fun x => iter n f x] is monotonic as well. *)

Variable leA : A -> A -> Prop.

Lemma iter_monotonic_in_x:
  forall f,
  monotonic leA leA f ->
  forall n,
  monotonic leA leA (iter n f).
Proof using.
  unfold monotonic. induction n; simpl; auto.
Qed.

(* Provided [leA] is a pre-order and [f] preserves [okA],
   [iter] preserves [inflationary okA leA]. *)

Variable leA_reflexive:
  forall a, leA a a.

Variable leA_transitive:
  forall a1 a2 a3, leA a1 a2 -> leA a2 a3 -> leA a1 a3.

Lemma iter_inflationary:
  forall f,
  preserves okA f ->
  inflationary okA leA f ->
  forall n,
  inflationary okA leA (iter n f).
Proof using leA_reflexive leA_transitive.
  (* The idea of the proof is simple. If [x <= f x] holds for every [x],
     then clearly [x <= f x <= f^2 x <= ... <= f^n x]. By reflexivity
     and transitivity, we obtain [x <= f^n x], which means that [f^n]
     is inflationary. *)
  intros ? ? hinfl.
  unfold inflationary.
  induction n; simpl; intros.
  eapply leA_reflexive.
  eapply leA_transitive.
    eapply hinfl. assumption.
    rewrite iter_iter_1.
    eauto.
Qed.

(* As a corollary of the above result, we find that, under the same
   hypotheses, [iter n f] is monotonic in [n]. *)

Lemma iter_monotonic_in_n:
  forall f,
  preserves okA f ->
  inflationary okA leA f ->
  monotonic le (pointwise okA leA) (fun n => iter n f).
Proof using leA_reflexive leA_transitive.
  unfold monotonic, inflationary, pointwise.
  intros f ? ? n1 n2 ? a ?.
  replace n2 with ((n2 - n1) + n1) by lia.
  rewrite iter_iter.
  assert (okA (iter n1 f a)).
    { eapply iter_preserves; eauto. }
  generalize dependent (iter n1 f a).
  generalize (n2 - n1).
  (* There remains to argue that [f^n] is inflationary. *)
  eapply iter_inflationary; assumption.
Qed.

(* As a re-statement, under the same hypotheses, [iter n f a] is
   monotonic in [n]. *)

Lemma iter_monotonic_in_n_specialized:
  forall f,
  preserves okA f ->
  inflationary okA leA f ->
  forall a,
  okA a ->
  monotonic le leA (fun n => iter n f a).
Proof using leA_reflexive leA_transitive.
  intros.
  eapply monotonic_pointwise_specialize with (f := fun n a => iter n f a).
  eauto using iter_monotonic_in_n.
  assumption.
Qed.

(* When restricted to monotonic functions [f],
  [fun f => iter n f x] is monotonic. *)

Lemma iter_monotonic_in_f:
  forall n a,
  monotonic
    (fun f1 f2 => monotonic leA leA f2 /\ pointwise (fun _ => True) leA f1 f2)
    leA
    (fun f => iter n f a).
Proof using leA_reflexive leA_transitive.
  unfold monotonic, pointwise.
  intros ? ? f1 f2 [ hmf2 hlef1f2 ].
  induction n; simpl.
  eauto.
  eapply leA_transitive.
  eapply hlef1f2. eauto.
  eapply hmf2. eauto.
Qed.

(* Iterating at least once takes us from [a] to at least [f a]. *)

Lemma iter_at_least_once:
  forall n,
  1 <= n ->
  forall f,
  preserves okA f ->
  inflationary okA leA f ->
  forall a,
  okA a ->
  leA (f a) (iter n f a).
Proof.
  intros. destruct n; [ lia | ].
  rewrite iter_iter_1p.
  eapply iter_inflationary; eauto.
Qed.

End Iter.
