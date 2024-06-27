Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Lia.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_soundness.

Section CK45_soundness.

Definition k45_frame := fun F => k4_frame F /\ k5_frame F.

Theorem CK45_Soundness : forall Γ phi, CK45H_prv Γ phi ->  loc_conseq k45_frame Γ phi.
Proof.
apply Soundness. pose correspond_k4. pose correspond_k5.
intro F ; split ; [intros H A HA | intros H ].
- destruct H. destruct HA as [ (B & C & J) | J] ; subst.
  + apply i ; auto.
  + apply i0 ; auto.
- split.
  + apply i. intros A B. apply H. left ; eexists ; eexists ; reflexivity.
  + apply i0. apply H. right ; reflexivity.
Qed.

End CK45_soundness.