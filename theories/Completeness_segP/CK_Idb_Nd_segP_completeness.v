From Stdlib Require Import List.
Export ListNotations.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_segP_completeness.

Axiom LEM : forall P, P \/ ~ P.

Section CK_Idb_Nd_completeness.

Definition is_Nd := (fun x => Nd = x).

Lemma CF_suff_Nd : suff_Nd_frame (CF is_Nd).
Proof.
intros w mwexpl.
destruct (LEM ((@head _ w) (◊ ⊥))).
*** assert (@head _ w = AllForm).
{ apply Extensionality_Ensembles ; split ; intros A HA ; unfold In, head in * ; cbn in *.
  - unfold AllForm ; auto.
  - apply (segClosed is_Nd) ; auto. eapply MP. apply EFQ.
    eapply MP. apply Ax. right. left. reflexivity.
    apply Id ; auto. }
apply cmreach_expl ; auto.
unfold cmreach ; cbn. rewrite H0. apply In_singleton.
*** exfalso. apply segP_noBot_noDiamBot in H. destruct H as (A & H & H0).
apply H0 in mwexpl. destruct mwexpl.
apply H2. unfold head. unfold expl ; cbn ; unfold AllForm ; auto.
apply Theory_AllForm. intro. apply H. apply (@segClosed _ w) ; auto. eapply MP.
apply EFQ. apply Id ; auto.
Qed.

Lemma CF_Nd : Nd_frame (CF is_Nd).
Proof.
apply suff_impl_Nd. apply CF_suff_Nd.
Qed.

Theorem suff_suff_CKIdbNd_Strong_Completeness : forall Γ φ,
    loc_conseq (fun F => suff_Idb_frame F /\ suff_Nd_frame F) Γ φ -> CKIdbNdH_prv Γ φ.
Proof.
intros. apply more_AdAx_more_prv with (AdAxIdb is_Nd).
- intros A HA. destruct HA ; auto.
- apply Strong_Completeness with (ClassF:= (fun F => suff_Idb_frame F /\ suff_Nd_frame F)) ; auto.
  split. apply CF_suff_Idb. apply CF_suff_Nd.
Qed.

Theorem suff_CKIdbNd_Strong_Completeness : forall Γ φ,
    loc_conseq (fun F => suff_Idb_frame F /\ Nd_frame F) Γ φ -> CKIdbNdH_prv Γ φ.
Proof.
intros. apply suff_suff_CKIdbNd_Strong_Completeness. intros M (HM4 & HM5) w Hw.
apply H ; auto. split ; auto. apply suff_impl_Nd ; auto.
Qed.

Theorem CKIdbNd_Strong_Completeness : forall Γ φ,
    loc_conseq (fun F => Idb_frame F /\ Nd_frame F) Γ φ -> CKIdbNdH_prv Γ φ.
Proof.
intros. apply suff_suff_CKIdbNd_Strong_Completeness. intros M (HM4 & HM5) w Hw.
apply H ; auto. split. apply suff_impl_Idb ; auto. apply suff_impl_Nd ; auto.
Qed.

End CK_Idb_Nd_completeness.