Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Lia.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_soundness.

Section WK_soundness.

Theorem WK_Soundness : forall Γ phi, (WKH_prv Γ phi) ->  (loc_conseq k5_frame Γ phi).
Proof.
apply Soundness. pose correspond_k5.
intro F ; split ; [intros H A HA ; inversion HA ; subst ; apply i ; auto | intros H ; apply i ; apply H ; unfold k5 ; auto].
Qed.

End WK_soundness.