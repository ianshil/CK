Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Lia.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_soundness.

Section CK_soundness.

Theorem CK_Soundness : forall Γ phi, (CKH_prv Γ phi) ->  (loc_conseq (fun x => True) Γ phi).
Proof.
apply Soundness. firstorder.
Qed.

End CK_soundness.

