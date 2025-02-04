Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Lia.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_soundness.

Section CK_Cd_Ndb_soundness.

Definition CdNdb_frame := fun F => Cd_frame F /\ Ndb_frame F.

Theorem CKCdNdb_Soundness : forall Γ phi, CKCdNdbH_prv Γ phi ->  loc_conseq CdNdb_frame Γ phi.
Proof.
apply Soundness. pose correspond_Cd. pose correspond_Ndb.
intro F ; intros H A HA ; destruct HA as [(B & C & J) | H0].
- destruct H. destruct J ; subst. apply i ; auto.
- subst ; apply i0 ; destruct H ; auto.
Qed.

End CK_Cd_Ndb_soundness.