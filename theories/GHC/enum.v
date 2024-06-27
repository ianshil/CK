Require Import Lia.
Require Import Coq.Arith.Cantor.
Require Import Coq.Logic.ConstructiveEpsilon.

Require Import im_syntax.

Require Import List.
Import ListNotations.

Fixpoint L_enum n :=
  match n with
  | 0 => [Bot]
  | S n => let LL := list_prod (L_enum n) (L_enum n)
          in L_enum n ++ [Var n]
                    ++ map (fun p => And (fst p) (snd p)) LL
                    ++ map (fun p => Or (fst p) (snd p)) LL
                    ++ map (fun p => Imp (fst p) (snd p)) LL
                    ++ map (fun p => Box (fst p)) LL
                    ++ map (fun p => Diam (fst p)) LL
  end.

Lemma L_enum_cumulative n m :
  n <= m -> incl (L_enum n) (L_enum m).
Proof.
  induction 1.
  - apply incl_refl.
  - eapply incl_tran; try apply IHle. cbn. apply incl_appl. apply incl_refl.
Qed.

Lemma L_enum_exhaustive A :
  exists n, In A (L_enum n).
Proof.
  induction A.
  - exists (S n). cbn. apply in_app_iff. right. now left.
  - exists 0. cbn. tauto.
  - destruct IHA1 as [n Hn], IHA2 as [m Hm]. exists (S (n + m)). cbn. apply in_app_iff.
    right. right. apply in_app_iff. left.
    apply in_map_iff. exists (A1, A2). cbn. split; trivial. apply in_prod.
    + eapply L_enum_cumulative; try apply Hn. lia.
    + eapply L_enum_cumulative; try apply Hm. lia.
  - destruct IHA1 as [n Hn], IHA2 as [m Hm]. exists (S (n + m)). cbn. apply in_app_iff.
    right. right. apply in_app_iff. right. apply in_app_iff. left.
    apply in_map_iff. exists (A1, A2). cbn. split; trivial. apply in_prod.
    + eapply L_enum_cumulative; try apply Hn. lia.
    + eapply L_enum_cumulative; try apply Hm. lia.
  - destruct IHA1 as [n Hn], IHA2 as [m Hm]. exists (S (n + m)). cbn. apply in_app_iff.
    right. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
    apply in_map_iff. exists (A1, A2). cbn. split; trivial. apply in_prod.
    + eapply L_enum_cumulative; try apply Hn. lia.
    + eapply L_enum_cumulative; try apply Hm. lia.
  - destruct IHA as [n Hn]. exists (S n). cbn. apply in_app_iff.
    right. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right.
     apply in_app_iff. left. apply in_map_iff. exists (A,A). cbn. split; trivial. apply in_prod ; auto.
  - destruct IHA as [n Hn]. exists (S n). cbn. apply in_app_iff.
    right. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right.
     apply in_app_iff. right. apply in_map_iff. exists (A,A). cbn. split; trivial. apply in_prod ; auto.
Qed.

Definition form_enum n :=
  let (k, l) := of_nat n in nth k (L_enum l) Bot.

Lemma form_enum_sur A :
  exists n, form_enum n = A.
Proof.
  destruct (L_enum_exhaustive A) as [l Hl].
  destruct (In_nth (L_enum l) A Bot Hl) as [k Hk].
  exists (to_nat (k, l)). unfold form_enum. rewrite cancel_of_to. apply Hk.
Qed.

Definition form_index' A :
  { n | form_enum n = A }.
Proof.
  apply constructive_indefinite_ground_description_nat.
  - decide equality. decide equality.
  - apply form_enum_sur.
Defined.

Definition form_index A :=
  proj1_sig (form_index' A).

Lemma form_enum_index A :
  form_enum (form_index A) = A.
Proof.
  unfold form_index. apply proj2_sig.
Qed.

Lemma form_index_inj A B :
  form_index A = form_index B -> A = B.
Proof.
  intros H. rewrite <- (form_enum_index A), <- (form_enum_index B). now rewrite H.
Qed.


