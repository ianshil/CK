From Stdlib Require Import List.
Export ListNotations.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_soundness.

Section IK_soundness.

Definition CdIdbNb_frame := fun F => Cd_frame F /\ Idb_frame F /\ Nd_frame F.

Theorem IK_Soundness : forall Γ phi, (IKH_prv Γ phi) ->  (loc_conseq CdIdbNb_frame Γ phi).
Proof.
apply Soundness. pose correspond_Cd. pose correspond_Idb. pose correspond_Nd.
intro F ; intros H A HA ; destruct HA as [ (B & C & J) | J] ; destruct H as (H0 & H1 & H2) ; subst.
- destruct J ; subst. apply i ; auto. apply i0 ; auto.
- apply i1 ; auto.
Qed.

End IK_soundness.