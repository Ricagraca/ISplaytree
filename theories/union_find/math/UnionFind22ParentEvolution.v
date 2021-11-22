Set Implicit Arguments.
From TLC Require Import LibTactics LibLogic LibProd LibContainer LibSet
     LibRelation LibPer LibMonoid.
Local Notation path := rtclosure.
From iris_time.union_find.math Require Import LibNatExtra LibIter
     InverseNatNat Ackermann InverseAckermann MiscArith TLCBuffer
     UnionFind01Data UnionFind03Link UnionFind04Compress UnionFind11Rank
     UnionFind21Parent.

Section ParentEvolution.

Variable V : Type.
Variable D : set V.
Variable F : binary V.
Variable K : V -> nat.
Hypothesis is_rdsf_F : is_rdsf D F K.

(* -------------------------------------------------------------------------- *)

(* During a link, a vertex [v] which already has a parent keeps this parent. *)

Lemma link_preserves_parent:
  forall x y v,
  is_root F x ->
  ~ is_root F v ->
  p F v = p (link F x y) v.
Proof using is_rdsf_F.
  intros.
  (* Let [parent] be the new parent of [v]. *)
  intro_parent (link F x y) v.
  (* Now, two cases arise: *)
  by_cases_on_link.
  { (* If [v] is not [x], then this edge existed before the link,
       so the [parent] is in fact the previous parent of [v]. *)
    eauto using parent_unique. }
  { (* If [v] is [x], we have a clear contradiction. *)
    tauto. }
Qed.

(* After a link, the parent of [x] is [y]. *)

Lemma link_sets_parent:
  forall x y,
  is_root F x ->
  p (link F x y) x = y.
Proof using is_rdsf_F.
  intros.
  (* Let [parent] be the new parent of [x]. *)
  intro_parent (link F x y) x.
  { eapply x_no_longer_a_root. }
  (* Now, two cases arise: *)
  by_cases_on_link.
  { (* [x] is a root and has an outgoing edge. Contradiction. *)
    false. eauto using a_root_has_no_parent. }
  { (* Obvious. *)
    tauto. }
Qed.

(* -------------------------------------------------------------------------- *)

(* During a compression, the only vertex whose parent changes is [x],
   and its new parent is [z]. *)

Lemma compress_changes_parent_of_x_only:
  forall x z v,
  ~ is_root F v ->
  p F v <> p (compress F x z) v ->
  v = x /\ p (compress F x z) v = z.
Proof using is_rdsf_F.
  intros.
  (* Let [parent] be the new parent of [v]. *)
  intro_parent (compress F x z) v.
  (* Now, two cases arise: *)
  by_cases_on_compress.
  { (* If [v] is not [x], then this edge existed before the compression,
       so [parent] is in fact the previous parent of [v]. This
       contradicts the hypothesis that the parent of [v] has changed. *)
    false. unfold not in *. eauto using parent_unique. }
  { (* If [v] is [x], we are done. *)
    eauto. }
Qed.

Lemma compress_changes_parent_of_x_to_z:
  forall x z,
  ~ is_root F x ->
  p (compress F x z) x = z.
Proof using is_rdsf_F.
  intros.
  intro_parent (compress F x z) x.
  by_cases_on_compress; tauto.
Qed.

Lemma compress_does_not_change_parent_of_v:
  forall x z v,
  ~ is_root F v ->
  v <> x ->
  p (compress F x z) v = p F v.
Proof using is_rdsf_F.
  intros.
  intro_parent (compress F x z) v.
  by_cases_on_compress.
  { symmetry. eauto using parent_unique. }
  { tauto. }
Qed.

End ParentEvolution.

