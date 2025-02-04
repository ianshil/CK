Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Lia.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_soundness.

Section CK_Cd_Idb_Ndb_soundness.

Definition CdIdbNdb_frame := fun F => Cd_frame F /\ Idb_frame F /\ Ndb_frame F.

Theorem CKCdIdbNdb_Soundness : forall Γ phi, (CKCdIdbNdbH_prv Γ phi) ->  (loc_conseq CdIdbNdb_frame Γ phi).
Proof.
apply Soundness. pose correspond_Cd. pose correspond_Idb. pose correspond_Ndb.
intro F ; intros H A HA ; destruct HA as [ (B & C & J) | J] ; destruct H as (H0 & H1 & H2) ; subst.
- destruct J ; subst. apply i ; auto. apply i0 ; auto.
- apply i1 ; auto.
Qed.

End CK_Cd_Idb_Ndb_soundness.