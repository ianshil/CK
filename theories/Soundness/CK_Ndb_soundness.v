From Stdlib Require Import List.
Export ListNotations.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Ensembles.


Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_soundness.

Section CK_Ndb_soundness.

Theorem CKNdb_Soundness : forall Γ phi, (CKNdbH_prv Γ phi) ->  (loc_conseq Ndb_frame Γ phi).
Proof.
apply Soundness. pose correspond_Ndb.
intro F ; intros H A HA ; inversion HA ; subst ; apply i ; auto.
Qed.

End CK_Ndb_soundness.