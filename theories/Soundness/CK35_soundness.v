Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Lia.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_soundness.

Section CK35_soundness.

Definition k35_frame := fun F => k3_frame F /\ k5_frame F.

Theorem CK35_Soundness : forall Γ phi, CK35H_prv Γ phi ->  loc_conseq k35_frame Γ phi.
Proof.
apply Soundness. pose correspond_k3. pose correspond_k5.
intro F ; split ; [intros H A HA | intros H ].
- destruct H. destruct HA as [ (B & C & J) | J] ; subst.
  + apply i ; auto.
  + apply i0 ; auto.
- split.
  + apply i. intros A B. apply H. left ; eexists ; eexists ; reflexivity.
  + apply i0. apply H. right ; reflexivity.
Qed.

End CK35_soundness.