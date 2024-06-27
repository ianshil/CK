Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Lia.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_soundness.

Section CK3Ndb_soundness.

Definition k3Ndb_frame := fun F => k3_frame F /\ Ndb_frame F.

Theorem CK3Ndb_Soundness : forall Γ phi, CK3NdbH_prv Γ phi ->  loc_conseq k3Ndb_frame Γ phi.
Proof.
apply Soundness. pose correspond_k3. pose correspond_Ndb.
intro F ; split ; [intros H A HA ; destruct HA as [(B & C & J) | H0] | intros H ].
- destruct H. destruct J ; subst. apply i ; auto.
- subst ; apply i0 ; destruct H ; auto.
- split.
  + apply i. intros A B. apply H. left ; eexists ; eexists ; reflexivity.
  + apply i0. auto.
Qed.

End CK3Ndb_soundness.