Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_segP_completeness.

Require Import Classical.

Section CK45_completeness.

Definition is_k5 := (fun x => k5 = x).

Lemma CF_suff_k5 : suff_k5_frame (CF is_k5).
Proof.
intros w mwexpl.
destruct (classic ((@head _ w) (⬦ ⊥))).
*** assert (@head _ w = AllForm).
{ apply Extensionality_Ensembles ; split ; intros A HA ; unfold In, head in * ; cbn in *.
  - unfold AllForm ; auto.
  - apply (segClosed is_k5) ; auto. eapply MP. apply EFQ.
    eapply MP. apply Ax. right. left. reflexivity.
    apply Id ; auto. }
apply cmreach_expl ; auto.
unfold cmreach ; cbn. rewrite H0. apply In_singleton.
*** exfalso. apply segP_noBot_noDiamBot in H. destruct H as (A & H & H0).
apply H0 in mwexpl. destruct mwexpl.
apply H2. unfold head. unfold expl ; cbn ; unfold AllForm ; auto.
apply Theory_AllForm. intro. apply H. apply (@segClosed _ w) ; auto. eapply MP.
apply EFQ. apply Id ; auto.
Qed.

Lemma CF_k5 : k5_frame (CF is_k5).
Proof.
apply suff_impl_k5. apply CF_suff_k5.
Qed.

Theorem suff_k45_Strong_Completeness : forall Γ φ,
    loc_conseq (fun F => suff_k4_frame F /\ suff_k5_frame F) Γ φ -> CK45H_prv Γ φ.
Proof.
intros. apply more_AdAx_more_prv with (AdAxk4 is_k5).
- intros A HA. destruct HA ; auto.
- apply Strong_Completeness with (FraP:= (fun F => suff_k4_frame F /\ suff_k5_frame F)) ; auto.
  split. apply CF_suff_k4. apply CF_suff_k5.
Qed.

Theorem suff_k4_Strong_Completeness : forall Γ φ,
    loc_conseq (fun F => suff_k4_frame F /\ k5_frame F) Γ φ -> CK45H_prv Γ φ.
Proof.
intros. apply suff_k45_Strong_Completeness. intros M (HM4 & HM5) w Hw.
apply H ; auto. split ; auto. apply suff_impl_k5 ; auto.
Qed.

Theorem Strong_Completeness : forall Γ φ,
    loc_conseq (fun F => k4_frame F /\ k5_frame F) Γ φ -> CK45H_prv Γ φ.
Proof.
intros. apply suff_k45_Strong_Completeness. intros M (HM4 & HM5) w Hw.
apply H ; auto. split. apply suff_impl_k4 ; auto. apply suff_impl_k5 ; auto.
Qed.

End CK45_completeness.