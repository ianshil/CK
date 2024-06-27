Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Lia.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_soundness.

Section CK3_soundness.

Theorem CK3_Soundness : forall Γ phi, (CK3H_prv Γ phi) ->  (loc_conseq k3_frame Γ phi).
Proof.
apply Soundness. pose correspond_k3.
intro F ; split ; [intros H A HA ; destruct HA as (B & C & J) ; subst ; apply i ; auto |
                       intros H ; apply i ; unfold k3 ; intros A B ; apply H ; eexists ; eexists ; reflexivity].
Qed.

End CK3_soundness.