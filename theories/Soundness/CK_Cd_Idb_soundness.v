Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Lia.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_soundness.

Section CK_Cd_Idb_soundness.

Definition CdIdb_frame := fun F => Cd_frame F /\ Idb_frame F.

Theorem CKCdIdb_Soundness : forall Γ phi, CKCdIdbH_prv Γ phi ->  loc_conseq CdIdb_frame Γ phi.
Proof.
apply Soundness. pose correspond_Cd. pose correspond_Idb.
intro F ; intros H A HA ; destruct HA as (B & C & J).
destruct H. destruct J ; subst. apply i ; auto. apply i0 ; auto.
Qed.

End CK_Cd_Idb_soundness.