Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Lia.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_soundness.

Section CKNdb_soundness.

Theorem CKNdb_Soundness : forall Γ phi, (CKNdbH_prv Γ phi) ->  (loc_conseq Ndb_frame Γ phi).
Proof.
apply Soundness. pose correspond_Ndb.
intro F ; split ; [intros H A HA ; inversion HA ; subst ; apply i ; auto | intros H ; apply i ; apply H ; unfold Ndb ; auto].
Qed.

End CKNdb_soundness.