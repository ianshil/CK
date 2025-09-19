From Stdlib Require Import List.
Export ListNotations.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_segP_completeness.


Section CK_Idb_completeness.

Definition NoAdAxIdb := (fun (ax : form) => False).

Theorem suff_CKIdb_Strong_Completeness : forall Γ φ,
    loc_conseq suff_Idb_frame Γ φ -> CKIdbH_prv Γ φ.
Proof.
intros. apply more_AdAx_more_prv with (AdAxIdb NoAdAxIdb).
- intros A HA. destruct HA ; auto. destruct H0 ; auto.
- apply Strong_Completeness with (suff_Idb_frame) ; auto.
  apply CF_suff_Idb.
Qed.

Theorem CKIdb_Strong_Completeness : forall Γ φ,
    loc_conseq Idb_frame Γ φ -> CKIdbH_prv Γ φ.
Proof.
intros. apply suff_CKIdb_Strong_Completeness.
intros M HM w Hw. apply H ; auto. apply suff_impl_Idb ; auto.
Qed.

End CK_Idb_completeness.