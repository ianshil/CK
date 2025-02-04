Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_segAB_completeness.


Section CK_Cd_Nd_completeness.

Definition is_Nd := (fun x => Nd = x).

Lemma CF_Nd : Nd_frame (CF is_Nd).
Proof.
intros w Hw.
assert (@head _ w = AllForm).
{ apply Extensionality_Ensembles ; split ; intros A HA ; unfold In, head in * ; cbn in *.
  - unfold AllForm ; auto.
  - apply (segClosed is_Nd) ; auto. eapply MP. apply EFQ.
    eapply MP. apply Ax. right. left. reflexivity.
    apply Id. apply (truth_lemma is_Nd).
    intros v Hv. apply Hw in Hv. exists (cexpl is_Nd). split ; auto.
    cbn ; auto. }
apply cmreach_expl ; auto.
unfold cmreach ; cbn. rewrite H. apply In_singleton.
Qed.

Theorem suff_CKCdNd_Strong_Completeness : forall Γ φ,
    loc_conseq (fun F => suff_Cd_frame F /\ Nd_frame F) Γ φ -> CKCdNdH_prv Γ φ.
Proof.
intros. apply more_AdAx_more_prv with (AdAxCd is_Nd).
- intros A HA. destruct HA ; auto.
- apply Strong_Completeness with (ClassF:=fun F => suff_Cd_frame F /\ Nd_frame F) ; auto.
  split ; [apply CF_suff_Cd | apply CF_Nd].
Qed.

Theorem CKCdNd_Strong_Completeness : forall Γ φ,
    loc_conseq (fun F => Cd_frame F /\ Nd_frame F) Γ φ -> CKCdNdH_prv Γ φ.
Proof.
intros. apply more_AdAx_more_prv with (AdAxCd is_Nd).
- intros A HA. destruct HA ; auto.
- apply Strong_Completeness with (ClassF:=fun F => Cd_frame F /\ Nd_frame F) ; auto.
  split ; [apply CF_Cd | apply CF_Nd].
Qed.

End CK_Cd_Nd_completeness.