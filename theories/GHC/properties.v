Require Import List.
Require Import ListDec.
Export ListNotations.
Require Import Arith.
Require Import Lia.
Require Import Ensembles.

Require Import general_export.

Require Import im_syntax.
Require Import CKH.
Require Import logic.

Lemma Thm_irrel : forall A B Γ , CKH_prv Γ (A -->  (B -->  A)).
Proof.
intros A B Γ. apply Ax. left ; eapply IA1 ; reflexivity.
Qed.

Lemma imp_Id_gen : forall A Γ , CKH_prv Γ (A -->  A).
Proof.
intros.
eapply MP. eapply MP.
apply Ax. left. apply IA2 with A (Top --> ⊥ --> Top) A ; reflexivity.
apply Ax. left. apply IA1 with A (Top --> ⊥ --> Top) ; reflexivity.
eapply MP.
apply Ax. left. apply IA1 with (Top --> ⊥ --> Top) A ; reflexivity.
apply Ax. left. apply IA1 with Top ⊥ ; reflexivity.
Qed.

Lemma comm_And_obj : forall A B Γ ,
    CKH_prv Γ (And A B -->  And B A).
Proof.
intros A B Γ . eapply MP. eapply MP.
apply Ax. left. apply IA8 with (And A B) B A ; reflexivity.
apply Ax. left. apply IA7 with A B ; reflexivity.
apply Ax. left. apply IA6 with A B ; reflexivity.
Qed.

Lemma comm_Or_obj : forall A B Γ, CKH_prv Γ (Or A B -->  Or B A).
Proof.
intros A B Γ. eapply MP. eapply MP.
apply Ax. left. apply IA5 with A B (Or B A) ; reflexivity.
apply Ax. left. apply IA4 with B A ; reflexivity.
apply Ax. left. apply IA3 with B A ; reflexivity.
Qed.

Lemma comm_Or : forall A B Γ, CKH_prv Γ (Or A B) -> CKH_prv Γ (Or B A).
Proof.
intros A B Γ D. eapply MP. apply comm_Or_obj. auto.
Qed.

Lemma EFQ : forall A Γ, CKH_prv Γ (Bot -->  A).
Proof.
intros A Γ. apply Ax. left ; eapply IA9 ; reflexivity.
Qed.

Lemma Imp_trans_help7 : forall x y z Γ, CKH_prv Γ ((x --> (y --> (z --> y)))).
Proof.
intros. eapply  MP. all: apply Ax ; left ; eapply IA1 ; reflexivity.
Qed.

Lemma Imp_trans_help8 : forall x y z Γ,
  CKH_prv Γ ((((x --> (y --> z)) --> (x --> y)) --> ((x --> (y --> z)) --> (x --> z)))).
Proof.
intros. eapply  MP. all: apply Ax ; left ; eapply IA2 ; reflexivity.
Qed.

Lemma Imp_trans_help9 : forall x y z u Γ,
  CKH_prv Γ ((x --> ((y --> (z --> u)) --> ((y --> z) --> (y --> u))))).
Proof.
intros. eapply  MP. all: apply Ax ; left.
eapply IA1 ; reflexivity. eapply IA2 ; reflexivity.
Qed.

Lemma Imp_trans_help14 : forall x y z u Γ,
  CKH_prv Γ ((x --> (y --> (z --> (u --> z))))).
Proof.
intros. eapply MP. apply Ax ; left ; eapply IA1 ; reflexivity. apply Imp_trans_help7.
Qed.

Lemma Imp_trans_help35 : forall x y z Γ, CKH_prv Γ ((x --> ((y --> x) --> z)) --> (x --> z)).
Proof.
intros. eapply  MP. apply Imp_trans_help8. apply Imp_trans_help7.
Qed.

Lemma Imp_trans_help37 : forall x y z u Γ, CKH_prv Γ (((x --> ((y --> (z --> y)) --> u)) --> (x --> u))).
Proof.
intros. eapply  MP. apply Imp_trans_help8. apply Imp_trans_help14.
Qed.

Lemma Imp_trans_help54 : forall x y z u Γ,
  CKH_prv Γ ((((x --> (y --> z)) --> (((x --> y) --> (x --> z)) --> u)) --> ((x --> (y --> z)) --> u))).
Proof.
intros. eapply  MP. apply Imp_trans_help8. apply Imp_trans_help9.
Qed.

Lemma Imp_trans_help170 : forall x y z Γ, CKH_prv Γ ((x --> y) --> ((z --> x) --> (z --> y))).
Proof.
intros. eapply  MP. apply Imp_trans_help35. apply Imp_trans_help9.
Qed.

Lemma Imp_trans_help410 : forall x y z Γ,
  CKH_prv Γ ((((x --> y) --> z) --> (y --> z))).
Proof.
intros. eapply MP. apply Imp_trans_help37. apply Imp_trans_help170.
Qed.

Lemma Imp_trans_help427 : forall x y z u Γ,
  CKH_prv Γ ((x --> (((y --> z) --> u) --> (z --> u)))).
Proof.
intros. eapply  MP. apply Ax ; left ; eapply IA1 ; reflexivity. apply Imp_trans_help410.
Qed.

Lemma Imp_trans : forall A B C Γ, CKH_prv Γ ((A --> B) -->  (B --> C) --> (A --> C)).
Proof.
intros. eapply  MP. eapply  MP. apply Imp_trans_help54. apply Imp_trans_help427.
apply Imp_trans_help170.
Qed.

Lemma monotR_Or : forall A B Γ ,
    CKH_prv Γ (A -->  B) ->
    forall C, CKH_prv Γ ((Or A C) -->  (Or B C)).
Proof.
intros A B Γ D C. eapply MP. eapply MP.
apply Ax ; left ; eapply IA5 ; reflexivity.
eapply MP. eapply MP. apply Imp_trans. exact D.
apply Ax ; left ; eapply IA3 ; reflexivity.
apply Ax ; left ; eapply IA4 ; reflexivity.
Qed.

Lemma monotL_Or : forall A B Γ,
    CKH_prv Γ (A -->  B) ->
    forall C, CKH_prv Γ ((Or C A) -->  (Or C B)).
Proof.
intros A B Γ D C. eapply MP. eapply MP.
apply Ax ; left ; eapply IA5 ; reflexivity.
apply Ax ; left ; eapply IA3 ; reflexivity.
eapply MP. eapply MP. apply Imp_trans. exact D.
apply Ax ; left ; eapply IA4 ; reflexivity.
Qed.

Lemma monot_Or2 : forall A B Γ, CKH_prv Γ (A -->  B) ->
    forall C, CKH_prv Γ ((Or A C) -->  (Or C B)).
Proof.
intros A B Γ D C.
eapply MP. eapply MP.
apply Ax ; left ; eapply IA5 ; reflexivity.
eapply MP. eapply MP. apply Imp_trans. exact D.
apply Ax ; left ; eapply IA4 ; reflexivity.
apply Ax ; left ; eapply IA3 ; reflexivity.
Qed.

Lemma prv_Top : forall Γ , CKH_prv Γ Top.
Proof.
intros. apply imp_Id_gen.
Qed.

Lemma absorp_Or1 : forall A Γ ,
    CKH_prv Γ (Or A (Bot)) ->
    CKH_prv Γ A.
Proof.
intros A Γ D. eapply MP. eapply MP. eapply MP.
apply Ax ; left ; eapply IA5 ; reflexivity.
apply imp_Id_gen. apply EFQ. auto.
Qed.

Lemma Imp_And : forall A B C Γ, CKH_prv Γ ((A -->  (B -->  C)) --> ((And A B) -->  C)).
Proof.
intros A B C Γ. eapply MP. eapply MP. apply Imp_trans. eapply MP. apply Imp_trans.
apply Ax ; left ; eapply IA6 ; reflexivity.
eapply MP. eapply MP.
apply Ax ; left ; eapply IA2 ; reflexivity.
apply Ax ; left ; eapply IA2 ; reflexivity.
eapply MP.
apply Ax ; left ; eapply IA1 ; reflexivity.
apply Ax ; left ; eapply IA7 ; reflexivity.
Qed.

Lemma Contr_Bot : forall A Γ, CKH_prv Γ (And A (Neg A) -->  (Bot)).
Proof.
intros A Γ . eapply MP. eapply MP. apply Imp_trans.
apply comm_And_obj. eapply MP. apply Imp_And.
apply imp_Id_gen.
Qed.

Theorem CKH_Detachment_Theorem : forall A B Γ,
           CKH_prv Γ (A --> B) ->
           CKH_prv  (Union _ Γ  (Singleton _ (A))) B.
Proof.
intros A B Γ D. eapply MP. apply (CKH_monot Γ (A --> B)) ; auto.
intros C HC. apply Union_introl ; auto.
apply Id. apply Union_intror. apply In_singleton.
Qed.

Theorem CKH_Deduction_Theorem : forall A B Γ,
           CKH_prv (Union _ Γ  (Singleton _ (A))) B ->
           CKH_prv Γ (A -->  B).
Proof.
intros. remember (Union form Γ (Singleton form A)) as L.
revert L B H A Γ HeqL.
intros L B D. induction D ; intros C Γ0 id ; subst.
(* Id *)
- inversion H ; subst ; cbn.
  + eapply MP. apply Thm_irrel. apply Id ; auto.
  + inversion H0 ; subst. apply imp_Id_gen.
(* Ax *)
- eapply MP. apply Thm_irrel. apply Ax ; assumption.
(* MP *)
- eapply MP. eapply MP. apply Imp_trans. eapply MP.
  eapply MP. apply Ax ; left ; eapply IA8 ; reflexivity. apply imp_Id_gen.
  apply IHD2 ; auto. eapply MP. apply Imp_And. apply IHD1 ; auto.
(* DNw *)
- eapply MP. apply Thm_irrel. eapply Nec ; auto.
Qed.

Lemma And_Imp : forall A B C Γ, CKH_prv Γ (((And A B) -->  C) --> (A --> (B -->  C))).
Proof.
intros. repeat apply CKH_Deduction_Theorem.
eapply MP. apply Id. apply Union_introl. apply Union_introl. apply Union_intror. apply In_singleton.
eapply MP. eapply MP. eapply MP.
apply Ax ; left ; eapply IA8 ; reflexivity.
apply CKH_Deduction_Theorem.
apply Id ; apply Union_introl ; apply Union_introl ; apply Union_intror ; apply In_singleton.
apply CKH_Deduction_Theorem.
apply Id ; apply Union_introl ; apply Union_intror ; apply In_singleton.
apply prv_Top.
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)

(* Some results about remove. *)

Lemma In_remove : forall (A : form) B (l : list (form)), List.In A (remove eq_dec_form B l) -> List.In A l.
Proof.
intros A B. induction l.
- cbn. auto.
- intro. cbn in H. destruct (eq_dec_form B a).
  * subst. apply in_cons. apply IHl. assumption.
  * inversion H.
    + subst. apply in_eq.
    + subst. apply in_cons. apply IHl. auto.
Qed.

Lemma InT_remove : forall (A : form) B (l : list (form)), InT A (remove eq_dec_form B l) -> InT A l.
Proof.
intros A B. induction l.
- cbn. auto.
- intro. cbn in H. destruct (eq_dec_form B a).
  * subst. apply InT_cons. apply IHl. assumption.
  * inversion H.
    + subst. apply InT_eq.
    + subst. apply InT_cons. apply IHl. auto.
Qed.

Lemma NoDup_remove : forall A (l : list (form)), NoDup l -> NoDup (remove eq_dec_form A l).
Proof.
intro A. induction l.
- intro. cbn. apply NoDup_nil.
- intro H. cbn. destruct (eq_dec_form A a).
  * subst. apply IHl. inversion H. assumption.
  * inversion H. subst. apply NoDup_cons. intro. apply H2. apply In_remove with (B:= A).
    assumption. apply IHl. assumption.
Qed.

(* To help for the Lindenbaum lemma. *)

Lemma Explosion : forall Γ A B,
  CKH_prv Γ ((B --> Bot) --> (B --> A)).
Proof.
intros. repeat apply CKH_Deduction_Theorem. eapply MP.
apply Ax ; left ; eapply IA9 ; reflexivity.
eapply MP. apply Id ; apply Union_introl ; apply Union_intror ; apply In_singleton.
apply Id ; apply Union_intror ; apply In_singleton.
Qed.

Lemma Imp_list_Imp : forall l Γ A B,
    CKH_prv Γ (list_Imp (A --> B) l) <->
    CKH_prv Γ (A --> list_Imp B l).
Proof.
induction l ; cbn ; intros.
- split ; intro ; auto.
- split ; intro.
  * repeat apply CKH_Deduction_Theorem.
    apply CKH_Detachment_Theorem in H. apply IHl in H.
    apply CKH_Detachment_Theorem in H. apply (CKH_monot _ _ H).
    intros C HC. inversion HC ; subst. inversion H0 ; subst.
    left. left ; auto. right ; auto. left ; right ; auto.
  * apply CKH_Deduction_Theorem. apply IHl.
    apply CKH_Deduction_Theorem. repeat apply CKH_Detachment_Theorem in H.
    apply (CKH_monot _ _ H).
    intros C HC. inversion HC ; subst. inversion H0 ; subst.
    left. left ; auto. right ; auto. left ; right ; auto.
Qed.

Lemma CKH_Imp_list_Detachment_Deduction_Theorem : forall l (Γ: Ensemble _) A,
    (forall B, (Γ B -> List.In B l) * (List.In B l -> Γ B)) ->
    (CKH_prv Γ A <-> CKH_prv (Empty_set _) (list_Imp A l)).
Proof.
induction l ; cbn ; intros ; split ; intros.
- apply (CKH_monot _ _ H0). intros B HB ; apply H in HB ; contradiction.
- apply (CKH_monot _ _ H0). intros B HB ; contradiction.
- destruct (In_form_dec l a).
  * apply IHl in H0. eapply MP. apply Thm_irrel. auto.
     intros. split ; intro. destruct (H B). destruct (o H2) ; subst ; auto.
     apply H ; auto.
  * apply Imp_list_Imp. apply (IHl (fun y => (In _ Γ y) /\ (y <> a))).
     intros. split ; intro. destruct H1. destruct (H B).
     apply o in H1. destruct H1 ; subst. exfalso. apply H2 ; auto.
     auto. split ; auto. apply H ; auto. intro. subst. auto.
     apply CKH_Deduction_Theorem ; auto.
     apply (CKH_monot _ _ H0). intros x Hx.
     destruct (eq_dec_form a x). subst. apply Union_intror. apply In_singleton.
     apply Union_introl. split ; auto.
- destruct (In_form_dec l a).
  * apply Imp_list_Imp in H0. eapply MP. apply IHl ; auto.
     intros. split ; intro. destruct (H B). destruct (o H1).
     subst. auto. auto. apply H. auto. exact H0. apply Id ; apply H ; auto.
  * apply Imp_list_Imp in H0. apply (IHl (fun y => (In _ Γ y) /\ (y <> a))) in H0.
     apply CKH_Detachment_Theorem in H0. apply (CKH_monot _ _ H0). intros x Hx.
     inversion Hx ; subst. inversion H1 ; subst ; auto. inversion H1 ; subst ; apply H ; auto.
     intros. split ; intro. destruct H2. destruct (H B).
     destruct (o H2) ; subst ; try contradiction ; auto.
     split ; auto. apply H ; auto. intro. subst. auto.
Qed.

Lemma K_list_Imp : forall l Γ A,
CKH_prv Γ (Box (list_Imp A l) --> list_Imp (Box A) (Box_list l)).
Proof.
induction l ; cbn ; intros.
- apply imp_Id_gen.
- repeat apply CKH_Deduction_Theorem. eapply MP. auto. eapply MP.
  eapply MP. apply Ax ; right ; eapply MAK1 ; reflexivity.
  apply Id ; left ; right ; apply In_singleton. apply Id ; right ;
  apply In_singleton.
Qed.

Lemma Box_distrib_list_Imp : forall l A,
    CKH_prv (Empty_set _) (list_Imp A l) ->
    CKH_prv (Empty_set _) (list_Imp (Box A) (Box_list l)).
Proof.
induction l ; cbn ; intros.
- eapply Nec ; auto.
- eapply MP. eapply MP. apply Imp_trans. eapply MP.
  apply Ax ; right ; eapply MAK1 ; reflexivity.
  eapply Nec ; auto. exact H. apply K_list_Imp.
Qed.

Lemma In_list_In_Box_list : forall l A,
    List.In A l -> List.In (Box A) (Box_list l).
Proof.
induction l ; intros ; cbn.
- inversion H.
- inversion H ;  subst ; auto.
Qed.

Lemma In_Box_list_In_list : forall l A,
     List.In A (Box_list l) -> (exists B, List.In B l /\ A = Box B).
Proof.
induction l ; cbn ; intros.
- inversion H.
- destruct H ; subst. exists a. split ; auto. apply IHl in H.
  destruct H. destruct H. subst. exists x ; auto.
Qed.

Lemma K_rule : forall Γ A, CKH_prv Γ A ->
    CKH_prv (fun x => (exists B, In _ Γ B /\ x = Box B)) (Box A).
Proof.
intros. apply CKH_finite in H. cbn in H.
destruct H as (X & HX1 & HX2 & (l & Hl)).
apply (CKH_monot (fun x1 : form => exists B : form, List.In B l /\ x1 = Box B)) ; cbn.
apply (CKH_Imp_list_Detachment_Deduction_Theorem l X A) in HX2.
apply Box_distrib_list_Imp in HX2.
epose (CKH_Imp_list_Detachment_Deduction_Theorem (Box_list l) _  (Box A)).
apply i in HX2 ; auto. exact HX2. intros. split ; intro. destruct H0. destruct H0. subst.
apply In_list_In_Box_list ; auto. apply In_Box_list_In_list in H0 ; auto.
intro. split ; intros ; apply Hl ; auto. intros C HC. inversion HC. destruct H. subst. unfold In.
exists x ; split ; auto. apply HX1. apply Hl ; auto.
Qed.

Fixpoint list_disj (l : list form) :=
match l with
 | nil => Bot
 | h :: t => Or h (list_disj t)
end.

Lemma remove_disj : forall l B Γ , CKH_prv Γ (list_disj l -->  Or B (list_disj (remove eq_dec_form B l))).
Proof.
induction l.
- intros. cbn. apply EFQ.
- intros. pose (IHl B Γ). cbn. destruct (eq_dec_form B a).
  * subst. cbn. eapply MP. eapply MP. apply Ax ; left ; eapply IA5 ; reflexivity.
    apply Ax ; left ; eapply IA3 ; reflexivity. auto.
  * cbn. eapply MP. eapply MP. apply Imp_trans. eapply MP. eapply MP.
    apply Ax ; left ; eapply IA5 ; reflexivity. apply Ax ; left ; eapply IA3 ; reflexivity.
    eapply MP. eapply MP. apply Imp_trans. exact c. apply Ax ; left ; eapply IA4 ; reflexivity.
    eapply MP. eapply MP. apply Ax ; left ; eapply IA5 ; reflexivity. eapply MP.
    eapply MP. apply Imp_trans. apply Ax ; left ; eapply IA3 ; reflexivity.
    apply Ax ; left ; eapply IA4 ; reflexivity. apply monotL_Or. apply Ax ; left ; eapply IA4 ; reflexivity.
Qed.


