From Stdlib Require Import List.
Export ListNotations.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_soundness.

Section WK_soundness.

Theorem WK_Soundness : forall Γ phi, (WKH_prv Γ phi) ->  (loc_conseq Nd_frame Γ phi).
Proof.
apply Soundness. pose correspond_Nd.
intro F ; intros H A HA ; inversion HA ; subst ; apply i ; auto.
Qed.

End WK_soundness.