From Stdlib Require Import List.
Export ListNotations.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_soundness.

Section CK_Cd_Nd_soundness.

Definition CdNd_frame := fun F => Cd_frame F /\ Nd_frame F.

Theorem CKCdNd_Soundness : forall Γ phi, CKCdNdH_prv Γ phi ->  loc_conseq CdNd_frame Γ phi.
Proof.
apply Soundness. pose correspond_Cd. pose correspond_Nd.
intro F ; intros H A HA ; destruct H ; destruct HA as [ (B & C & J) | J] ; subst.
- apply i ; auto.
- apply i0 ; auto.
Qed.

End CK_Cd_Nd_soundness.