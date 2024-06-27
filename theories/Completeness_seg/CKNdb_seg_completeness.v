Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_seg_completeness.



Section CKNdb_completeness.

Definition is_Ndb := (fun x => Ndb = x).

Lemma CF_Ndb Γ : Ndb_frame (CF is_Ndb Γ).
Proof.
intros w Hw u v iwu muv.
pose (Hw _ iwu).
assert (@head _ _ v = Clos Γ).
{ apply Extensionality_Ensembles ; split ; intros A HA ; unfold In, head in * ; cbn in *.
  - apply (segInclClos is_Ndb) in HA ; auto.
  - apply (segClosed is_Ndb) ; auto. eapply MP. apply EFQ. apply Id. unfold In ; cbn.
    apply (boxreflect is_Ndb) with (A:=⊥) in muv ; auto.
    apply (@segClosed is_Ndb _ u) ; auto. 2: unfold Clos ; auto.
    eapply MP. apply Ax. right. reflexivity.
    apply Id. apply (truth_lemma is_Ndb). unfold Clos ; auto.
    intros z Hz. exists (cexpl is_Ndb Γ). split ; auto.
    2: cbn ; auto. apply Hw. apply cireach_trans with u ; auto. }
apply cmreach_expl ; auto.
unfold cmreach ; cbn. rewrite H. apply In_singleton.
Qed.

Theorem CKNdb_Strong_Completeness : forall Γ φ,
    loc_conseq Ndb_frame Γ φ -> CKNdbH_prv Γ φ.
Proof.
apply Strong_Completeness with (FraP:= Ndb_frame) ; auto.
apply CF_Ndb.
Qed.

End CKNdb_completeness.
