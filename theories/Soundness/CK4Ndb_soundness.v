Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Lia.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_soundness.

Section CK4Ndb_soundness.

Definition k4Ndb_frame := fun F => Ndb_frame F /\ k4_frame F.

Theorem CK4Ndb_Soundness : forall Γ phi, CK4NdbH_prv Γ phi ->  loc_conseq k4Ndb_frame Γ phi.
Proof.
apply Soundness. pose correspond_Ndb. pose correspond_k4.
intro F ; split ; [intros H A HA ; destruct HA as [(B & C & J) | H0] | intros H ].
- destruct H. destruct J ; subst. apply i0 ; auto.
- destruct H ; subst. apply i ; auto.
- split.
  + apply i. intros A B. apply H ; auto.
  + apply i0. intros A B. apply H. left ; eexists ; eexists ; reflexivity.
Qed.

End CK4Ndb_soundness.