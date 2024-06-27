Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Lia.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_soundness.

Section CK34_soundness.

Definition k34_frame := fun F => k3_frame F /\ k4_frame F.

Theorem CK34_Soundness : forall Γ phi, CK34H_prv Γ phi ->  loc_conseq k34_frame Γ phi.
Proof.
apply Soundness. pose correspond_k3. pose correspond_k4.
intro F ; split ; [intros H A HA ; destruct HA as (B & C & J) | intros H ].
- destruct H. destruct J ; subst. apply i ; auto. apply i0 ; auto.
- split.
  + apply i. intros A B. apply H. eexists ; eexists ; left ; reflexivity.
  + apply i0. intros A B. apply H. eexists ; eexists ; right ; reflexivity.
Qed.

End CK34_soundness.