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

Section CK3Ndb_completeness.

Definition is_Ndb := (fun x => Ndb = x).

Lemma CF_Ndb : Ndb_frame (CF is_Ndb).
Proof.
intros w Hw u v iwu muv.
pose (Hw _ iwu).
assert (@head _ v = AllForm).
{ apply Extensionality_Ensembles ; split ; intros A HA ; unfold In, head in * ; cbn in *.
  - unfold AllForm ; auto.
  - apply (segClosed is_Ndb) ; auto. eapply MP. apply EFQ. apply Id. unfold In ; cbn.
    apply (boxreflect is_Ndb) with (A:=⊥) in muv ; auto.
    apply (@segClosed is_Ndb u) ; auto.
    eapply MP. apply Ax. right ; left. reflexivity.
    apply Id. apply (truth_lemma is_Ndb). unfold Clos ; auto.
    intros z Hz. exists (cexpl is_Ndb). split ; auto.
    2: cbn ; auto. apply Hw. apply cireach_trans with u ; auto. }
apply cmreach_expl ; auto.
unfold cmreach ; cbn. rewrite H. apply In_singleton.
Qed.

Theorem Strong_Completeness : forall Γ φ,
    loc_conseq (fun F => k3_frame F /\ Ndb_frame F) Γ φ -> CK3NdbH_prv Γ φ.
Proof.
intros. apply more_AdAx_more_prv with (AdAxk3 is_Ndb).
- intros A HA. destruct HA ; auto.
- apply Strong_Completeness with (FraP:= (fun F => k3_frame F /\ Ndb_frame F)) ; auto.
  split. apply CF_k3. apply CF_Ndb.
Qed.

End CK3Ndb_completeness.