From Stdlib Require Import List.
Export ListNotations.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_th_completeness.

Section CK_Cd_Idb_completeness.

Definition NoAdAxCdIdb := (fun (ax : form) => False).

Theorem suff_suff_CKCdIdb_Strong_Completeness : forall Γ φ,
    loc_conseq (fun F => suff_Cd_frame F /\ suff_Idb_frame F) Γ φ -> CKCdIdbH_prv Γ φ.
Proof.
intros. apply more_AdAx_more_prv with (AdAxCdIdb NoAdAxCdIdb).
- intros A HA. destruct HA ; auto. destruct H0 ; auto.
- apply Strong_Completeness with (ClassF:= fun F => suff_Cd_frame F /\ suff_Idb_frame F) ; auto.
  repeat split ; auto.
  + apply strong_is_suff_Cd. apply CF_strong_Cd_weak_Idb.
  + apply CF_suff_Idb.
Qed.

Theorem CKCdIdb_Strong_Completeness : forall Γ φ,
    loc_conseq (fun F => Cd_frame F /\ Idb_frame F) Γ φ -> CKCdIdbH_prv Γ φ.
Proof.
intros. apply more_AdAx_more_prv with (AdAxCdIdb NoAdAxCdIdb).
- intros A HA. destruct HA ; auto. destruct H0 ; auto.
- apply Strong_Completeness with (ClassF:= fun F => Cd_frame F /\ Idb_frame F) ; auto.
  apply CF_CdIdb.
Qed.

End CK_Cd_Idb_completeness.
