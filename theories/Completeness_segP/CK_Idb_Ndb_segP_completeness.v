Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_segP_completeness.


Axiom LEM : forall P, P \/ ~ P.

Section CK_Idb_Ndb_completeness.

Definition is_Ndb := (fun x => Ndb = x).

Lemma CF_suff_Ndb : suff_Ndb_frame (CF is_Ndb).
Proof.
intros w mwexpl v mwv.
destruct (LEM ((@head _ w) (⬦ ⊥))).
*** assert (@head _ v = AllForm).
{ apply Extensionality_Ensembles ; split ; intros A HA ; unfold In, head in * ; cbn in *.
  - unfold AllForm ; auto.
  - apply (@segClosed is_Ndb v) ; auto. eapply MP. apply EFQ.
    apply Id. unfold In ; cbn.
    apply (boxreflect is_Ndb) with (A:=⊥) in mwv ; auto.
    apply (@segClosed is_Ndb w) ; auto.
    eapply MP. apply Ax. right ; left ; reflexivity.
    apply Id. auto. }
apply cmreach_expl ; auto.
unfold cmreach ; cbn. rewrite H0. apply In_singleton.
*** exfalso. apply segP_noBot_noDiamBot in H. destruct H as (A & H & H0).
apply H0 in mwexpl. destruct mwexpl.
apply H2. unfold head. unfold expl ; cbn ; unfold AllForm ; auto.
apply Theory_AllForm. intro. apply H. apply (@segClosed _ w) ; auto. eapply MP.
apply EFQ. apply Id ; auto.
Qed.

Lemma CF_Ndb : Ndb_frame (CF is_Ndb).
Proof.
apply suff_impl_Ndb. apply CF_suff_Ndb.
Qed.

Theorem suff_suff_CKIdbNdb_Strong_Completeness : forall Γ φ,
    loc_conseq (fun F => suff_Idb_frame F /\ suff_Ndb_frame F) Γ φ -> CKIdbNdbH_prv Γ φ.
Proof.
intros. apply more_AdAx_more_prv with (AdAxIdb is_Ndb).
- intros A HA. destruct HA ; auto.
- apply Strong_Completeness with (ClassF:= (fun F => suff_Idb_frame F /\ suff_Ndb_frame F)) ; auto.
  split. apply CF_suff_Idb. apply CF_suff_Ndb.
Qed.

Theorem suff_CKIdbNdb_Strong_Completeness : forall Γ φ,
    loc_conseq (fun F => suff_Idb_frame F /\ Ndb_frame F) Γ φ -> CKIdbNdbH_prv Γ φ.
Proof.
intros. apply suff_suff_CKIdbNdb_Strong_Completeness. intros M (HM4 & HMNdb) w Hw.
apply H ; auto. split ; auto. apply suff_impl_Ndb ; auto.
Qed.

Theorem CKIdbNdb_Strong_Completeness : forall Γ φ,
    loc_conseq (fun F => Idb_frame F /\ Ndb_frame F) Γ φ -> CKIdbNdbH_prv Γ φ.
Proof.
intros. apply suff_suff_CKIdbNdb_Strong_Completeness. intros M (HM4 & HMNdb) w Hw.
apply H ; auto. split. apply suff_impl_Idb ; auto. apply suff_impl_Ndb ; auto.
Qed.

End CK_Idb_Ndb_completeness.