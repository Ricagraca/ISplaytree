Set Implicit Arguments.
From TLC Require Import LibTactics LibLogic LibProd LibContainer LibSet
     LibRelation LibPer.
Local Notation path := rtclosure.
From iris_time.union_find.math Require Import TLCBuffer
     UnionFind01Data UnionFind06Join UnionFind11Rank.

(* The union of two separate ranked disjoint set forests is again a ranked disjoint
   set forest. *)

Section Join.

Variable V : Type.
Variable D1 D2 : set V.
Variable F1 F2 : binary V.
Variable K1 K2 : V -> nat.

Hypothesis disjointness:
  D1 \# D2.

Hypothesis hrdsf1:
  is_rdsf D1 F1 K1.

Hypothesis hrdsf2:
  is_rdsf D2 F2 K2.

(* If [x] is in [D1], then [K x] is [K1 x], and similarly on the other side. *)

Lemma rank_union_inversion_1:
  forall x,
  x \in D1 ->
  (fun x => If x \in D1 then K1 x else K2 x) x = K1 x.
Proof using.
  clear disjointness hrdsf1 hrdsf2.
  intros. simpl. cases_if~.
Qed.

Lemma rank_union_inversion_2:
  forall x,
  x \in D2 ->
  (fun x => If x \in D1 then K1 x else K2 x) x = K2 x.
Proof using disjointness.
  clear hrdsf1 hrdsf2.
  intros. simpl. cases_if~. false. rew_set in *.
Qed.

(* The result. *)

Lemma is_rdsf_join:
  is_rdsf (D1 \u D2) (union F1 F2) (fun x => If x \in D1 then K1 x else K2 x).
Proof using disjointness hrdsf1 hrdsf2.
  unfold is_rdsf in *. intros. splits.
  (* [is_dsf] *)
  { eauto using is_dsf_join with is_dsf. }
  (* [rank_increases_along_edges] *)
  { intros x y [ F1xy | F2xy ].
    { assert (x \in D1). { eauto with is_dsf confined. }
      assert (y \in D1). { eauto with is_dsf confined. }
      repeat cases_if. intuition eauto. }
    { assert (x \in D2). { eauto with is_dsf confined. }
      assert (y \in D2). { eauto with is_dsf confined. }
      assert (x \notin D1). { intro. rew_set in *. }
      assert (y \notin D1). { intro. rew_set in *. }
      repeat cases_if. intuition eauto. }
  }
  (* [numerous_family] *)
  { intros r. rewrite is_root_join. intros [ Hr1 Hr2 ].
    destruct (classic (r \in D1 \u D2)); [ destruct (classic (r \in D1)) | ].
    (* Case: [r \in D1]. *)
    { erewrite descendants_join_1 by eauto with is_dsf confined.
      rewrite rank_union_inversion_1 by eauto.
      intuition eauto. }
    (* Case: [r \in D2]. *)
    { assert (r \in D2). { rew_set in *. tauto. }
      erewrite descendants_join_2 by eauto with is_dsf confined.
      rewrite rank_union_inversion_2 by eauto.
      intuition eauto. }
    (* Case: [r \notin D1 \u D2]. *)
    { assert (r \notin D1 /\ r \notin D2).
      { rew_set in *. tauto. }
      cases_if. { rew_set in *. tauto. }
      assert (h: K2 r = 0). { intuition eauto. }
      rewrite h. simpl.
      eapply card_ge_one.
      { unfold descendants. rew_set. eauto with rtclosure. }
      { eapply finite_descendants.
        eauto using is_dsf_join with is_dsf.
        intuition eauto using finite_union with is_dsf. }
    }
  }
  (* [finite] *)
  { intuition eauto using finite_union. }
  (* zero outside the domain *)
  { intros x Dx. rew_set in *. cases_if; intuition eauto. }
Qed.

End Join.

