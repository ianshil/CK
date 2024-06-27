Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Lia.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_soundness.

Section CK4_soundness.

Theorem CK4_Soundness : forall Γ phi, (CK4H_prv Γ phi) ->  (loc_conseq k4_frame Γ phi).
Proof.
apply Soundness. pose correspond_k4.
intro F ; split ; [intros H A HA ; destruct HA as (B & C & J) ; subst ; apply i ; auto |
                       intros H ; apply i ; unfold k4 ; intros A B ; apply H ; eexists ; eexists ; reflexivity].
Qed.

End CK4_soundness.