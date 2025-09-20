From Stdlib Require Import List.
Export ListNotations.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_soundness.

Section CK_Idb_Ndb_soundness.

Definition IdbNdb_frame := fun F => Ndb_frame F /\ Idb_frame F.

Theorem CKIdbNdb_Soundness : forall Γ phi, CKIdbNdbH_prv Γ phi ->  loc_conseq IdbNdb_frame Γ phi.
Proof.
apply Soundness. pose correspond_Ndb. pose correspond_Idb.
intro F ; intros H A HA ; destruct HA as [(B & C & J) | H0].
- destruct H. destruct J ; subst. apply i0 ; auto.
- destruct H ; subst. apply i ; auto.
Qed.

End CK_Idb_Ndb_soundness.