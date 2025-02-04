Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Lia.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.

Section general_soundness.

(* We can show that all axioms of CK are valid on all
    models of our semantics. *)

Lemma Ax_valid : forall A, Axioms A ->
  (forall M w, forces M w A).
Proof.
intros A Ax. destruct Ax as [Ax | Ax].
(* Intuitionistic axioms *)
+ inversion Ax ; cbn ; intros ; subst ; cbn ; intros ; auto.
  - apply Persistence with (w:=v) ; auto.
  - apply H0 with v1 ; auto. apply ireach_tran with v0 ; auto. apply ireach_refl.
  - destruct H4 ; auto. apply H0 ; auto. apply ireach_tran with v0 ; auto.
  - destruct H0 ; auto.
  - destruct H0 ; auto.
  - split. apply H0 ; auto. apply ireach_tran with v0 ; auto. apply H2 ; auto.
  - subst. apply Expl.
(* Modal axioms *)
+ inversion Ax ; cbn ; intros ; subst ; cbn ; intros.
  (* K1 *)
  - apply H0 with v1 u ; auto. apply ireach_tran with v0 ; auto. apply ireach_refl.
    apply H2 with v1 ; auto.
  (* K2 *)
  - destruct (H2 _ H3) as (u & Hu1 & Hu2). exists u. split ; auto. apply H0 with v1 u ; auto.
    apply ireach_tran with v0 ; auto. apply ireach_refl.
Qed.

(* We can then show that if a certain class of frames validates a set of
    additional axioms, then we obtain a soundness result on this class
    of frames. *)

Variable AdAx : form -> Prop.
Variable FraP : frame -> Prop.
Hypothesis corresp_AdAx_FraP : forall F, FraP F -> (forall A, AdAx A -> fvalid F A).

Theorem Soundness : forall Γ phi, (extCKH_prv AdAx Γ phi) ->  (loc_conseq FraP Γ phi).
Proof.
intros Γ phi D. induction D ; intros C FrProp w Hw.
(* Id *)
- apply Hw ; auto.
(* Ax *)
- destruct H.
  + apply Ax_valid ; destruct H ; firstorder.
  + apply (corresp_AdAx_FraP fra FrProp A H) ; auto.
(* MP *)
- unfold loc_conseq in *. cbn in *. apply IHD1 with w ; auto. apply ireach_refl.
(* Nec *)
- subst. unfold loc_conseq in *. cbn in *. intros. apply IHD ; auto.
  intros ; contradiction.
Qed.

End general_soundness.