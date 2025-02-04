Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Lia.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_soundness.

Section CK_Idb_Nd_soundness.

Definition IdbNd_frame := fun F => Idb_frame F /\ Nd_frame F.

Theorem CKIdbNd_Soundness : forall Γ phi, CKIdbNdH_prv Γ phi ->  loc_conseq IdbNd_frame Γ phi.
Proof.
apply Soundness. pose correspond_Idb. pose correspond_Nd.
intro F ; intros H A HA ; destruct H ; destruct HA as [ (B & C & J) | J] ; subst.
- apply i ; auto.
- apply i0 ; auto.
Qed.

End CK_Idb_Nd_soundness.