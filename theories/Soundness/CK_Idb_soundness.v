Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Lia.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_soundness.

Section CK_Idb_soundness.

Theorem CKIdb_Soundness : forall Γ phi, (CKIdbH_prv Γ phi) ->  (loc_conseq Idb_frame Γ phi).
Proof.
apply Soundness. pose correspond_Idb.
intro F ; intros H A HA ; destruct HA as (B & C & J) ; subst ; apply i ; auto.
Qed.

End CK_Idb_soundness.