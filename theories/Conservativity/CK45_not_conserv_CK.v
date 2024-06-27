Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Ensembles.
Require Import Bool.
Require Import Btauto.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import CK_soundness.
Require Import conserv_prelims.

Require Import Classical.

Section negneg_box.

Variable AdAx: form -> Prop.
Definition AdAxk45 := fun x => AdAx x \/ (k5 = x \/ exists A B, (k4 A B) = x).

Lemma negneg_box_prv : forall Γ φ, extCKH_prv AdAxk45 Γ ((¬ ¬ ☐ φ) --> ☐ ¬ ¬ φ).
Proof.
intros.
eapply MP. eapply MP. apply Imp_trans.
2: apply Ax ; right ; right ; right ; exists (¬ φ), ⊥ ; reflexivity.
eapply MP. eapply MP. apply Imp_trans.
- apply extCKH_Deduction_Theorem. apply extCKH_Deduction_Theorem.
  eapply MP. apply Id ; left ; right ; split. apply extCKH_Deduction_Theorem.
  apply extCKH_monot with (Union _ (Union _ Γ (Singleton _ (☐ φ))) (Singleton _ (⬦¬φ))).
  apply extCKH_Detachment_Theorem.
  eapply MP. eapply MP. apply Imp_trans. 2: apply Ax ; right ; right ; left ; reflexivity.
  eapply MP. apply Ax ; left ; right ; eapply k2 ; reflexivity.
  apply extCKH_Detachment_Theorem.
  eapply MP. apply Ax ; left ; right ; eapply k1 ; reflexivity.
  apply Nec. repeat apply extCKH_Deduction_Theorem.
  eapply MP. apply Id ; right ; split. apply Id ; left ; right ; split.
  intros A HA ; inversion HA ; subst. inversion H ; subst. left ; left ; left ; auto.
  inversion H0 ; subst. right ; split. inversion H ; subst. left. right ; split.
- apply extCKH_Deduction_Theorem.
  eapply MP. eapply extCKH_Detachment_Theorem.
  apply Imp_trans. apply EFQ.
Qed.

End negneg_box.





Section CK45_not_conserv_CK.

Theorem diam_free_ext_CK45_CK : forall Γ φ, (forall ψ, (Γ ψ \/ φ = ψ) -> diam_free ψ) ->
              CKH_prv Γ φ -> CK45H_prv Γ φ.
Proof.
intros. apply more_AdAx_more_prv with (fun x => False) ; auto. intros A F ; contradiction.
Qed.

(* Intuitionistic relation *)

Definition bireach (b0 b1 : bool * bool) : Prop :=
  if eqb (fst b0) (fst b1) then (if eqb (snd b0) (snd b1) then True else False) else
    if fst b1 then (if eqb (snd b0) (snd b1) then True else False) else False.

Lemma bireach_refl b : bireach b b.
Proof.
unfold bireach ; destruct b ; repeat rewrite eqb_reflx ; cbn ; auto.
Qed.

Lemma bireach_trans u v w: bireach u v -> bireach v w -> bireach u w.
Proof.
intros ; unfold bireach in *. destruct w ; destruct v ; destruct u ; cbn in * ; auto.
destruct (eqb b3 b1) eqn:E0; destruct (eqb b4 b2) eqn:E1; destruct (eqb b1 b) eqn:E2;
destruct (eqb b2 b0) eqn:E3; destruct (eqb b3 b) eqn:E4; destruct (eqb b4 b0) eqn:E5;
cbn in * ; try apply eqb_prop in E0 ; try apply eqb_prop in E1 ; try apply eqb_prop in E2 ;
try apply eqb_prop in E3 ; try apply eqb_prop in E4 ; try apply eqb_prop in E5 ; subst ;
firstorder. 1,3,4,5,9,10,11: destruct b0 ; cbn in E5 ; discriminate.
destruct b ; cbn in E4 ; discriminate. destruct b ; cbn in E2 ; discriminate.
1,4:destruct b0 ; cbn in E3 ; discriminate. destruct b0 ; cbn in E5 ; discriminate.
1,4,5,6,7:destruct b,b1 ; cbn in * ; auto. destruct b ; cbn in E0 ; discriminate.
destruct b0 ; cbn in E1 ; discriminate.
Qed.

Lemma bireach_expl u : bireach (true,true) u -> u = (true,true).
Proof.
intros. unfold bireach in H ; destruct u ; cbn in * ; auto.
destruct b,b0; try rewrite eqb_iff in H ; firstorder.
Qed.

(* Modal relation *)

Definition bmreach (b0 b1 : bool * bool) : Prop :=
  if fst b1 then (if snd b1 then (if fst b0 then True else False) else False) else
    if negb (fst b0) then (if negb (snd b0) then (if negb (fst b1) then (if snd b1 then True else False) else False) else False) else False.

Lemma bmreach_expl u : bmreach (true,true) u <-> u = (true,true).
Proof.
split ; unfold bmreach ; intro ; destruct u ; cbn in * ; subst ; destruct b ; destruct b0 ; inversion H ; subst ; firstorder.
Qed.

(* We can define a frame. *)

Instance bF : frame :=
      {|
        nodes := bool * bool ;
        expl:= (true,true) ;

        ireachable := bireach ;
        ireach_refl := bireach_refl ;
        ireach_tran := bireach_trans ;
        ireach_expl := bireach_expl  ;

        mreachable := bmreach  ;
        mreach_expl := bmreach_expl  ;
      |}.

(* We define a valuation. *)

Definition bval (b : bool * bool) (p : nat) := if fst b then (if snd b then True else False) else False.

Lemma bval_persist : forall u v, bireach u v -> forall (p : nat), bval u p -> bval v p.
Proof.
intros. unfold bval in *. destruct u ; destruct v ; destruct b ; destruct b0 ; destruct b1 ; destruct b2 ; cbn in * ; auto.
Qed.

Lemma bval_expl  : forall p, bval expl p.
Proof.
intros. unfold bval. destruct expl eqn:E; destruct b ; destruct b0 ; cbn ; auto. all: inversion E.
Qed.

(* Finally we can define a model. *)

Instance bM : model :=
      {|
        fra := bF ;

        val := bval  ;
        persist :=  bval_persist ;
        val_expl :=  bval_expl
      |}.

Theorem diam_free_strict_ext_CK45_CK : CK45H_prv (Empty_set _) ((¬ ¬ ☐ ⊥) --> ☐ ⊥) /\
                                                                     ~ CKH_prv (Empty_set _) ((¬ ¬ ☐ ⊥) --> ☐ ⊥).
Proof.
split.
- eapply MP. eapply MP. apply Imp_trans.
  apply more_AdAx_more_prv with (AdAxk45 (fun _ : form => False)).
  intros A HA. destruct HA. contradiction. destruct H ; subst ; auto.
  apply negneg_box_prv.
  eapply MP. apply Ax ; left ; right ; eapply k1 ; reflexivity.
  apply Nec. apply extCKH_Deduction_Theorem. eapply MP.
  apply Id ; right ; split. apply imp_Id_gen.
- intro. apply extCKH_Detachment_Theorem in H. apply CK_Soundness in H.
  assert (forces bM (false,false) ((¬ (¬ (☐ ⊥))))).
  { intros b ifb Hb. destruct b ; cbn in * ; unfold bireach in ifb ; cbn in ifb.
    destruct b ; cbn in *.
    - destruct b0 ; cbn in * ; auto. apply Hb. unfold bireach ; cbn ; auto.
      intros. destruct v. unfold bireach in H0 ; cbn in *. destruct b. destruct b0.
      contradiction. destruct u. unfold bmreach in H1 ; destruct b ; destruct b0 ; cbn in * ; firstorder.
      contradiction.
    - destruct b0. contradiction. enough ((true,false) = (true,true)). inversion H0.
      apply Hb. unfold bireach ; cbn ; auto. intros. destruct v. unfold bireach in H0 ; cbn in *. destruct b. destruct b0.
      contradiction. destruct u. unfold bmreach in H1 ; destruct b ; destruct b0 ; cbn in * ; firstorder.
      contradiction. }
  assert (~ forces bM (false,false) (☐ ⊥)).
  { intro. cbn in H1. enough ((false,true) = (true,true)). inversion H2.
    apply H1 with (false,false). unfold bireach ; cbn ; auto. unfold bmreach ; cbn ; auto. }
  apply H1. apply H ; auto.
  intros. inversion H2 ; subst ; auto. inversion H3. inversion H3 ; auto.
Qed.

End CK45_not_conserv_CK.






Section IK_not_conserv_CK.

Theorem diam_free_ext_IK_CK : forall Γ φ, (forall ψ, (Γ ψ \/ φ = ψ) -> diam_free ψ) ->
              CKH_prv Γ φ -> IKH_prv Γ φ.
Proof.
intros. apply more_AdAx_more_prv with (fun x => False) ; auto. intros A F ; contradiction.
Qed.

Theorem diam_free_strict_ext_IK_CK : IKH_prv (Empty_set _) ((¬ ¬ ☐ ⊥) --> ☐ ⊥) /\
                                                                     ~ CKH_prv (Empty_set _) ((¬ ¬ ☐ ⊥) --> ☐ ⊥).
Proof.
split.
- apply more_AdAx_more_prv with (fun x => (exists A B, k4 A B = x) \/ k5 = x).
  intros A HA ; firstorder.
  apply diam_free_strict_ext_CK45_CK.
- apply diam_free_strict_ext_CK45_CK.
Qed.

End IK_not_conserv_CK.





