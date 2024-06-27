Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_segAB_completeness.

Require Import Classical.

Section CK35_completeness.

Definition is_k5 := (fun x => k5 = x).

Lemma CF_k5 : k5_frame (CF is_k5).
Proof.
intros w Hw.
assert (@head _ w = AllForm).
{ apply Extensionality_Ensembles ; split ; intros A HA ; unfold In, head in * ; cbn in *.
  - unfold AllForm ; auto.
  - apply (segClosed is_k5) ; auto. eapply MP. apply EFQ.
    eapply MP. apply Ax. right. left. reflexivity.
    apply Id. apply (truth_lemma is_k5).
    intros v Hv. apply Hw in Hv. exists (cexpl is_k5). split ; auto.
    cbn ; auto. }
apply cmreach_expl ; auto.
unfold cmreach ; cbn. rewrite H. apply In_singleton.
Qed.

Theorem Strong_Completeness : forall Γ φ,
    loc_conseq (fun F => k3_frame F /\ k5_frame F) Γ φ -> CK35H_prv Γ φ.
Proof.
intros. apply more_AdAx_more_prv with (AdAxk3 is_k5).
- intros A HA. destruct HA ; auto.
- apply Strong_Completeness with (FraP:= (fun F => k3_frame F /\ k5_frame F)) ; auto.
  split. apply CF_k3. apply CF_k5.
Qed.

End CK35_completeness.