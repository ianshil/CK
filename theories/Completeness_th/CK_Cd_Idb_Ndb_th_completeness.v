Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_th_completeness.

Section CK_Cd_Idb_Ndb_completeness.

Definition is_Ndb := (fun x => Ndb = x).

Lemma CF_suff_Ndb : suff_Ndb_frame (CF is_Ndb).
Proof.
intros w (H & H0) v (H1 & H2).
apply cworld_prf_irrel.
apply Extensionality_Ensembles ; split ; intros A HA ; unfold In, head in * ; cbn in *.
- unfold AllForm ; auto.
- apply (Closed is_Ndb) ; auto. eapply MP. apply EFQ.
  apply Id. apply H1. apply (Closed is_Ndb) ; auto.
  eapply MP. apply Ax. right. left. reflexivity. apply Id.
  apply H0 ; auto.
Qed.

Lemma CF_Ndb : Ndb_frame (CF is_Ndb).
Proof.
apply suff_impl_Ndb. apply CF_suff_Ndb.
Qed.

Theorem suff_suff_suff_CKCdIdbNdb_Strong_Completeness : forall Γ φ,
    loc_conseq (fun F => suff_Cd_frame F /\ suff_Idb_frame F /\ suff_Ndb_frame F) Γ φ -> CKCdIdbNdbH_prv Γ φ.
Proof.
intros. apply more_AdAx_more_prv with (AdAxCdIdb is_Ndb).
- intros A HA. destruct HA ; auto.
- apply Strong_Completeness with (ClassF:= fun F => suff_Cd_frame F /\ suff_Idb_frame F /\ suff_Ndb_frame F) ; auto.
  repeat split ; auto.
  + apply strong_is_suff_Cd. apply CF_strong_Cd_weak_Idb.
  + apply CF_suff_Idb.
  + apply CF_suff_Ndb.
Qed.

Theorem CKCdIdbNdb_Strong_Completeness : forall Γ φ,
    loc_conseq (fun F => Cd_frame F /\ Idb_frame F /\ Ndb_frame F) Γ φ -> CKCdIdbNdbH_prv Γ φ.
Proof.
intros. apply more_AdAx_more_prv with (AdAxCdIdb is_Ndb).
- intros A HA. destruct HA ; auto.
- apply Strong_Completeness with (ClassF:= fun F => Cd_frame F /\ Idb_frame F /\ Ndb_frame F) ; auto.
  repeat split ; auto. 1-2: apply CF_CdIdb. apply CF_Ndb.
Qed.

End CK_Cd_Idb_Ndb_completeness.