From Stdlib Require Import List.
Export ListNotations.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_soundness.

Section CK_Cd_soundness.

Theorem CKCd_Soundness : forall Γ phi, (CKCdH_prv Γ phi) ->  (loc_conseq Cd_frame Γ phi).
Proof.
apply Soundness. pose correspond_Cd.
intro F ; intros H A HA ; destruct HA as (B & C & J) ; subst ; apply i ; auto.
Qed.

End CK_Cd_soundness.