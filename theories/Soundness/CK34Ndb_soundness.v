Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Lia.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_soundness.

Section IK_soundness.

Definition k34Ndb_frame := fun F => k3_frame F /\ k4_frame F /\ Ndb_frame F.

Theorem CK34Ndb_Soundness : forall Γ phi, (CK34NdbH_prv Γ phi) ->  (loc_conseq k34Ndb_frame Γ phi).
Proof.
apply Soundness. pose correspond_k3. pose correspond_k4. pose correspond_Ndb.
intro F ; split ; [intros H A HA | intros H ].
- destruct HA as [ (B & C & J) | J] ; destruct H as (H0 & H1 & H2) ; subst.
  + destruct J ; subst. apply i ; auto. apply i0 ; auto.
  + apply i1 ; auto.
- repeat split.
  + apply i. intros A B. apply H. left ; eexists ; eexists ; left ; reflexivity.
  + apply i0. intros A B. apply H. left ; eexists ; eexists ; right ; reflexivity.
  + apply i1. apply H. right ; reflexivity.
Qed.

End IK_soundness.