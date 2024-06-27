Require Import List.
Require Import ListDec.
Export ListNotations.
Require Import Arith.
Require Import Lia.
Require Import Ensembles.

Require Import general_export.

Require Import im_syntax.
Require Import CKH.
Require Import logic.
Require Import properties.
Require Import Lindenbaum_lem.
Require Import Lindenbaum_lem_pair.

Require Import Classical.

Section classical_facts.

  (* To prove strong completeness, we require the strength of classical
      logic. For this, we declare LEM as an axiom. *)

Lemma LEM_prime Δ :
  quasi_prime Δ  -> prime Δ .
Proof.
  intros H1 A B H2.
  apply H1 in H2 ; auto. destruct (classic (Δ  A)) ; auto.
  destruct (classic (Δ  B)) ; auto. exfalso. apply H2.
  intro. destruct H3 ; auto.
Qed.

Variable AdAx : form -> Prop.

Lemma list_split_union : forall l Γ0 Γ1,
  (forall A : form, List.In A l -> (Union form Γ0 Γ1) A) ->
  exists l1, forall A : form, (Γ1 A -> List.In A l -> List.In A l1) /\ (List.In A l1 -> (Γ1 A /\ List.In A l)).
Proof.
induction l ; cbn ; intros.
- exists []. intros ; split ; intros ; auto. inversion H0.
- assert ((Union form Γ0 Γ1) a). apply H ; auto.
  inversion H0 ; subst.
  + destruct (classic (Γ1 a)).
     { destruct (IHl Γ0 Γ1).
       intros A HA. apply H. auto. exists (a :: x). intros. split ; intros ; cbn ; auto.
       destruct H5 ; subst ; cbn ; auto. right. apply H3 ; auto.
       split ; auto. inversion H4 ; subst ; auto. apply H3 in H5 ; firstorder.
       inversion H4 ; subst ; auto. apply H3 in H5 ; firstorder. }
     { destruct (IHl Γ0 Γ1).
       intros A HA. apply H. auto. exists x. intros. split ; intros ; cbn ; auto.
       destruct H5 ; subst ; cbn ; auto. exfalso ; auto. apply H3 ; auto.
       split ; auto. apply H3 in H4 ; firstorder.
       apply H3 in H4 ; firstorder. }
  + destruct (IHl Γ0 Γ1).
     intros A HA. apply H. auto. exists (a :: x). intros. split ; intros ; cbn ; auto.
     destruct H4 ; subst ; cbn ; auto. right. apply H2 ; auto.
     split ; auto. inversion H3 ; subst ; auto. apply H2 in H4 ; firstorder.
     inversion H3 ; subst ; auto. apply H2 in H4 ; firstorder.
Qed.

Lemma partial_finite : forall Γ0 Γ1 A,
    extCKH_prv AdAx (Union _ Γ0 Γ1) A ->
    exists l1, (forall A : form, List.In A l1 -> Γ1 A) /\
    extCKH_prv AdAx (Union _ Γ0 (fun x => List.In x l1)) A.
Proof.
intros. destruct (extCKH_finite _ _ _ H) as (Γ2 & H0 & H1 & l & H2).
destruct (list_split_union l Γ0 Γ1) as (l1 & H3); auto. intros. apply H0 ; apply H2 ; auto.
exists l1. split ; auto.
- intros. apply H3 in H4. destruct H4 ; auto.
- apply (extCKH_monot _ _ _ H1). intros B HB. assert (List.In B l).
  apply H2 ; auto. apply H0 in HB. inversion HB ; subst. left ; auto.
  right. apply H3 ; auto.
Qed.

End classical_facts.