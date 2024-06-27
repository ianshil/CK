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

Section theorems_and_meta.

Variable AdAx : form -> Prop.

Lemma Thm_irrel : forall A B Γ , extCKH_prv AdAx Γ (A -->  (B -->  A)).
Proof.
intros A B Γ. apply Ax. left ; left ; eapply IA1 ; reflexivity.
Qed.

Lemma imp_Id_gen : forall A Γ , extCKH_prv AdAx Γ (A -->  A).
Proof.
intros.
eapply MP. eapply MP.
apply Ax. left ; left. apply IA2 with A (Top --> ⊥ --> Top) A ; reflexivity.
apply Ax. left ; left. apply IA1 with A (Top --> ⊥ --> Top) ; reflexivity.
eapply MP.
apply Ax. left ; left. apply IA1 with (Top --> ⊥ --> Top) A ; reflexivity.
apply Ax. left ; left. apply IA1 with Top ⊥ ; reflexivity.
Qed.

Lemma comm_And_obj : forall A B Γ ,
    extCKH_prv AdAx Γ (And A B -->  And B A).
Proof.
intros A B Γ . eapply MP. eapply MP.
apply Ax. left ; left. apply IA8 with (And A B) B A ; reflexivity.
apply Ax. left ; left. apply IA7 with A B ; reflexivity.
apply Ax. left ; left. apply IA6 with A B ; reflexivity.
Qed.

Lemma comm_Or_obj : forall A B Γ, extCKH_prv AdAx Γ (Or A B -->  Or B A).
Proof.
intros A B Γ. eapply MP. eapply MP.
apply Ax. left ; left. apply IA5 with A B (Or B A) ; reflexivity.
apply Ax. left ; left. apply IA4 with B A ; reflexivity.
apply Ax. left ; left. apply IA3 with B A ; reflexivity.
Qed.

Lemma comm_Or : forall A B Γ, extCKH_prv AdAx Γ (Or A B) -> extCKH_prv AdAx Γ (Or B A).
Proof.
intros A B Γ D. eapply MP. apply comm_Or_obj. auto.
Qed.

Lemma EFQ : forall A Γ, extCKH_prv AdAx Γ (Bot -->  A).
Proof.
intros A Γ. apply Ax. left ; left ; eapply IA9 ; reflexivity.
Qed.

Lemma Imp_trans_help7 : forall x y z Γ, extCKH_prv AdAx Γ ((x --> (y --> (z --> y)))).
Proof.
intros. eapply  MP. all: apply Ax ; left ; left ; eapply IA1 ; reflexivity.
Qed.

Lemma Imp_trans_help8 : forall x y z Γ,
  extCKH_prv AdAx Γ ((((x --> (y --> z)) --> (x --> y)) --> ((x --> (y --> z)) --> (x --> z)))).
Proof.
intros. eapply  MP. all: apply Ax ; left ; left ; eapply IA2 ; reflexivity.
Qed.

Lemma Imp_trans_help9 : forall x y z u Γ,
  extCKH_prv AdAx Γ ((x --> ((y --> (z --> u)) --> ((y --> z) --> (y --> u))))).
Proof.
intros. eapply  MP. all: apply Ax ; left ; left.
eapply IA1 ; reflexivity. eapply IA2 ; reflexivity.
Qed.

Lemma Imp_trans_help14 : forall x y z u Γ,
  extCKH_prv AdAx Γ ((x --> (y --> (z --> (u --> z))))).
Proof.
intros. eapply MP. apply Ax ; left ; left ; eapply IA1 ; reflexivity. apply Imp_trans_help7.
Qed.

Lemma Imp_trans_help35 : forall x y z Γ, extCKH_prv AdAx Γ ((x --> ((y --> x) --> z)) --> (x --> z)).
Proof.
intros. eapply  MP. apply Imp_trans_help8. apply Imp_trans_help7.
Qed.

Lemma Imp_trans_help37 : forall x y z u Γ, extCKH_prv AdAx Γ (((x --> ((y --> (z --> y)) --> u)) --> (x --> u))).
Proof.
intros. eapply  MP. apply Imp_trans_help8. apply Imp_trans_help14.
Qed.

Lemma Imp_trans_help54 : forall x y z u Γ,
  extCKH_prv AdAx Γ ((((x --> (y --> z)) --> (((x --> y) --> (x --> z)) --> u)) --> ((x --> (y --> z)) --> u))).
Proof.
intros. eapply  MP. apply Imp_trans_help8. apply Imp_trans_help9.
Qed.

Lemma Imp_trans_help170 : forall x y z Γ, extCKH_prv AdAx Γ ((x --> y) --> ((z --> x) --> (z --> y))).
Proof.
intros. eapply  MP. apply Imp_trans_help35. apply Imp_trans_help9.
Qed.

Lemma Imp_trans_help410 : forall x y z Γ,
  extCKH_prv AdAx Γ ((((x --> y) --> z) --> (y --> z))).
Proof.
intros. eapply MP. apply Imp_trans_help37. apply Imp_trans_help170.
Qed.

Lemma Imp_trans_help427 : forall x y z u Γ,
  extCKH_prv AdAx Γ ((x --> (((y --> z) --> u) --> (z --> u)))).
Proof.
intros. eapply  MP. apply Ax ; left ; left ; eapply IA1 ; reflexivity. apply Imp_trans_help410.
Qed.

Lemma Imp_trans : forall A B C Γ, extCKH_prv AdAx Γ ((A --> B) -->  (B --> C) --> (A --> C)).
Proof.
intros. eapply  MP. eapply  MP. apply Imp_trans_help54. apply Imp_trans_help427.
apply Imp_trans_help170.
Qed.

Lemma monotR_Or : forall A B Γ ,
    extCKH_prv AdAx Γ (A -->  B) ->
    forall C, extCKH_prv AdAx Γ ((Or A C) -->  (Or B C)).
Proof.
intros A B Γ D C. eapply MP. eapply MP.
apply Ax ; left ; left ; eapply IA5 ; reflexivity.
eapply MP. eapply MP. apply Imp_trans. exact D.
apply Ax ; left ; left ; eapply IA3 ; reflexivity.
apply Ax ; left ; left ; eapply IA4 ; reflexivity.
Qed.

Lemma monotL_Or : forall A B Γ,
    extCKH_prv AdAx Γ (A -->  B) ->
    forall C, extCKH_prv AdAx Γ ((Or C A) -->  (Or C B)).
Proof.
intros A B Γ D C. eapply MP. eapply MP.
apply Ax ; left ; left ; eapply IA5 ; reflexivity.
apply Ax ; left ; left ; eapply IA3 ; reflexivity.
eapply MP. eapply MP. apply Imp_trans. exact D.
apply Ax ; left ; left ; eapply IA4 ; reflexivity.
Qed.

Lemma monot_Or2 : forall A B Γ, extCKH_prv AdAx Γ (A -->  B) ->
    forall C, extCKH_prv AdAx Γ ((Or A C) -->  (Or C B)).
Proof.
intros A B Γ D C.
eapply MP. eapply MP.
apply Ax ; left ; left ; eapply IA5 ; reflexivity.
eapply MP. eapply MP. apply Imp_trans. exact D.
apply Ax ; left ; left ; eapply IA4 ; reflexivity.
apply Ax ; left ; left ; eapply IA3 ; reflexivity.
Qed.

Lemma prv_Top : forall Γ , extCKH_prv AdAx Γ Top.
Proof.
intros. apply imp_Id_gen.
Qed.

Lemma absorp_Or1 : forall A Γ ,
    extCKH_prv AdAx Γ (Or A (Bot)) ->
    extCKH_prv AdAx Γ A.
Proof.
intros A Γ D. eapply MP. eapply MP. eapply MP.
apply Ax ; left ; left ; eapply IA5 ; reflexivity.
apply imp_Id_gen. apply EFQ. auto.
Qed.

Lemma Imp_And : forall A B C Γ, extCKH_prv AdAx Γ ((A -->  (B -->  C)) --> ((And A B) -->  C)).
Proof.
intros A B C Γ. eapply MP. eapply MP. apply Imp_trans. eapply MP. apply Imp_trans.
apply Ax ; left ; left ; eapply IA6 ; reflexivity.
eapply MP. eapply MP.
apply Ax ; left ; left ; eapply IA2 ; reflexivity.
apply Ax ; left ; left ; eapply IA2 ; reflexivity.
eapply MP.
apply Ax ; left ; left ; eapply IA1 ; reflexivity.
apply Ax ; left ; left ; eapply IA7 ; reflexivity.
Qed.

Lemma Contr_Bot : forall A Γ, extCKH_prv AdAx Γ (And A (Neg A) -->  (Bot)).
Proof.
intros A Γ . eapply MP. eapply MP. apply Imp_trans.
apply comm_And_obj. eapply MP. apply Imp_And.
apply imp_Id_gen.
Qed.

Theorem extCKH_Detachment_Theorem : forall A B Γ,
           extCKH_prv AdAx Γ (A --> B) ->
           extCKH_prv AdAx  (Union _ Γ  (Singleton _ (A))) B.
Proof.
intros A B Γ D. eapply MP. apply (extCKH_monot _ Γ (A --> B)) ; auto.
intros C HC. apply Union_introl ; auto.
apply Id. apply Union_intror. apply In_singleton.
Qed.

Theorem extCKH_Deduction_Theorem : forall A B Γ,
           extCKH_prv AdAx (Union _ Γ  (Singleton _ (A))) B ->
           extCKH_prv AdAx Γ (A -->  B).
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
  eapply MP. apply Ax ; left ; left ; eapply IA8 ; reflexivity. apply imp_Id_gen.
  apply IHD2 ; auto. eapply MP. apply Imp_And. apply IHD1 ; auto.
(* DNw *)
- eapply MP. apply Thm_irrel. eapply Nec ; auto.
Qed.

Lemma And_Imp : forall A B C Γ, extCKH_prv AdAx Γ (((And A B) -->  C) --> (A --> (B -->  C))).
Proof.
intros. repeat apply extCKH_Deduction_Theorem.
eapply MP. apply Id. apply Union_introl. apply Union_introl. apply Union_intror. apply In_singleton.
eapply MP. eapply MP. eapply MP.
apply Ax ; left ; left ; eapply IA8 ; reflexivity.
apply extCKH_Deduction_Theorem.
apply Id ; apply Union_introl ; apply Union_introl ; apply Union_intror ; apply In_singleton.
apply extCKH_Deduction_Theorem.
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
  extCKH_prv AdAx Γ ((B --> Bot) --> (B --> A)).
Proof.
intros. repeat apply extCKH_Deduction_Theorem. eapply MP.
apply Ax ; left ; left ; eapply IA9 ; reflexivity.
eapply MP. apply Id ; apply Union_introl ; apply Union_intror ; apply In_singleton.
apply Id ; apply Union_intror ; apply In_singleton.
Qed.

Lemma Imp_list_Imp : forall l Γ A B,
    extCKH_prv AdAx Γ (list_Imp (A --> B) l) <->
    extCKH_prv AdAx Γ (A --> list_Imp B l).
Proof.
induction l ; cbn ; intros.
- split ; intro ; auto.
- split ; intro.
  * repeat apply extCKH_Deduction_Theorem.
    apply extCKH_Detachment_Theorem in H. apply IHl in H.
    apply extCKH_Detachment_Theorem in H. apply (extCKH_monot _ _ _ H).
    intros C HC. inversion HC ; subst. inversion H0 ; subst.
    left. left ; auto. right ; auto. left ; right ; auto.
  * apply extCKH_Deduction_Theorem. apply IHl.
    apply extCKH_Deduction_Theorem. repeat apply extCKH_Detachment_Theorem in H.
    apply (extCKH_monot _ _ _ H).
    intros C HC. inversion HC ; subst. inversion H0 ; subst.
    left. left ; auto. right ; auto. left ; right ; auto.
Qed.

Lemma extCKH_Imp_list_Detachment_Deduction_Theorem : forall l (Γ: Ensemble _) A,
    (forall B, (Γ B -> List.In B l) * (List.In B l -> Γ B)) ->
    (extCKH_prv AdAx Γ A <-> extCKH_prv AdAx (Empty_set _) (list_Imp A l)).
Proof.
induction l ; cbn ; intros ; split ; intros.
- apply (extCKH_monot _ _ _ H0). intros B HB ; apply H in HB ; contradiction.
- apply (extCKH_monot _ _ _ H0). intros B HB ; contradiction.
- destruct (In_form_dec l a).
  * apply IHl in H0. eapply MP. apply Thm_irrel. auto.
     intros. split ; intro. destruct (H B). destruct (o H2) ; subst ; auto.
     apply H ; auto.
  * apply Imp_list_Imp. apply (IHl (fun y => (In _ Γ y) /\ (y <> a))).
     intros. split ; intro. destruct H1. destruct (H B).
     apply o in H1. destruct H1 ; subst. exfalso. apply H2 ; auto.
     auto. split ; auto. apply H ; auto. intro. subst. auto.
     apply extCKH_Deduction_Theorem ; auto.
     apply (extCKH_monot _ _ _ H0). intros x Hx.
     destruct (eq_dec_form a x). subst. apply Union_intror. apply In_singleton.
     apply Union_introl. split ; auto.
- destruct (In_form_dec l a).
  * apply Imp_list_Imp in H0. eapply MP. apply IHl ; auto.
     intros. split ; intro. destruct (H B). destruct (o H1).
     subst. auto. auto. apply H. auto. exact H0. apply Id ; apply H ; auto.
  * apply Imp_list_Imp in H0. apply (IHl (fun y => (In _ Γ y) /\ (y <> a))) in H0.
     apply extCKH_Detachment_Theorem in H0. apply (extCKH_monot _ _ _ H0). intros x Hx.
     inversion Hx ; subst. inversion H1 ; subst ; auto. inversion H1 ; subst ; apply H ; auto.
     intros. split ; intro. destruct H2. destruct (H B).
     destruct (o H2) ; subst ; try contradiction ; auto.
     split ; auto. apply H ; auto. intro. subst. auto.
Qed.

Lemma K_list_Imp : forall l Γ A,
extCKH_prv AdAx Γ (Box (list_Imp A l) --> list_Imp (Box A) (Box_list l)).
Proof.
induction l ; cbn ; intros.
- apply imp_Id_gen.
- repeat apply extCKH_Deduction_Theorem. eapply MP. auto. eapply MP.
  eapply MP. apply Ax ; left ; right ; eapply Kb ; reflexivity.
  apply Id ; left ; right ; apply In_singleton. apply Id ; right ;
  apply In_singleton.
Qed.

Lemma Box_distrib_list_Imp : forall l A,
    extCKH_prv AdAx (Empty_set _) (list_Imp A l) ->
    extCKH_prv AdAx (Empty_set _) (list_Imp (Box A) (Box_list l)).
Proof.
induction l ; cbn ; intros.
- eapply Nec ; auto.
- eapply MP. eapply MP. apply Imp_trans. eapply MP.
  apply Ax ; left ; right ; eapply Kb ; reflexivity.
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

Lemma K_rule : forall Γ A, extCKH_prv AdAx Γ A ->
    extCKH_prv AdAx (fun x => (exists B, In _ Γ B /\ x = Box B)) (Box A).
Proof.
intros. apply extCKH_finite in H. cbn in H.
destruct H as (X & HX1 & HX2 & (l & Hl)).
apply (extCKH_monot _ (fun x1 : form => exists B : form, List.In B l /\ x1 = Box B)) ; cbn.
apply (extCKH_Imp_list_Detachment_Deduction_Theorem l X A) in HX2.
apply Box_distrib_list_Imp in HX2.
epose (extCKH_Imp_list_Detachment_Deduction_Theorem (Box_list l) _  (Box A)).
apply i in HX2 ; auto. exact HX2. intros. split ; intro. destruct H0. destruct H0. subst.
apply In_list_In_Box_list ; auto. apply In_Box_list_In_list in H0 ; auto.
intro. split ; intros ; apply Hl ; auto. intros C HC. inversion HC. destruct H. subst. unfold In.
exists x ; split ; auto. apply HX1. apply Hl ; auto.
Qed.



Section list_of_disjunctions.

Fixpoint list_disj (l : list form) :=
match l with
 | nil => Bot
 | h :: t => Or h (list_disj t)
end.

Lemma list_disj_map_Box : forall l, (forall A, List.In A l -> exists B, A = ☐ B) ->
                exists l', l = map Box l'.
Proof.
induction l ; cbn ; intros ; auto.
- exists [] ; auto.
- destruct (H a) ; auto ; subst.
  destruct (IHl). intros. apply H ; auto. subst.
  exists (x :: x0). cbn ; auto.
Qed.

Lemma remove_disj : forall l B Γ , extCKH_prv AdAx Γ (list_disj l -->  Or B (list_disj (remove eq_dec_form B l))).
Proof.
induction l.
- intros. cbn. apply EFQ.
- intros. pose (IHl B Γ). cbn. destruct (eq_dec_form B a).
  * subst. cbn. eapply MP. eapply MP. apply Ax ; left ; left ; eapply IA5 ; reflexivity.
    apply Ax ; left ; left ; eapply IA3 ; reflexivity. auto.
  * cbn. eapply MP. eapply MP. apply Imp_trans. eapply MP. eapply MP.
    apply Ax ; left ; left ; eapply IA5 ; reflexivity. apply Ax ; left ; left ; eapply IA3 ; reflexivity.
    eapply MP. eapply MP. apply Imp_trans. exact e. apply Ax ; left ; left ; eapply IA4 ; reflexivity.
    eapply MP. eapply MP. apply Ax ; left ; left ; eapply IA5 ; reflexivity. eapply MP.
    eapply MP. apply Imp_trans. apply Ax ; left ; left ; eapply IA3 ; reflexivity.
    apply Ax ; left ; left ; eapply IA4 ; reflexivity. apply monotL_Or. apply Ax ; left ; left ; eapply IA4 ; reflexivity.
Qed.

Lemma IdL_list_disj_obj : forall Γ l0 l1,
  extCKH_prv AdAx Γ (list_disj l0 --> list_disj (l0 ++ l1)).
Proof.
induction l0 ; intros.
- simpl. apply EFQ.
- simpl. apply monotL_Or. apply IHl0.
Qed.

Lemma IdR_list_disj_obj : forall Γ l0 l1,
  extCKH_prv AdAx Γ (list_disj l1 --> list_disj (l0 ++ l1)).
Proof.
induction l0 ; intros.
- simpl. apply imp_Id_gen.
- simpl. eapply MP. eapply MP. apply Imp_trans.
  apply IHl0. apply Ax ; left ; left ; eapply IA4 ; reflexivity.
Qed.

Lemma IdL_list_disj : forall Γ l0 l1,
  extCKH_prv AdAx Γ (list_disj l0) ->
  extCKH_prv AdAx Γ (list_disj (l0 ++ l1)).
Proof.
intros. eapply MP. apply IdL_list_disj_obj. auto.
Qed.

Lemma IdR_list_disj : forall Γ l0 l1,
  extCKH_prv AdAx Γ (list_disj l1) -> 
  extCKH_prv AdAx Γ (list_disj (l0 ++ l1)).
Proof.
intros. eapply MP. apply IdR_list_disj_obj. auto.
Qed.

Lemma forall_list_disj : forall l Γ A,
  extCKH_prv AdAx Γ (list_disj l) ->
  (forall B, List.In B l -> extCKH_prv AdAx Γ (B --> A)) ->
  extCKH_prv AdAx Γ A.
Proof.
induction l ; cbn ; intros ; auto.
- eapply MP. apply EFQ. auto.
- eapply MP. eapply MP. eapply MP.
  apply Ax ; left ; left ; eapply IA5 ; reflexivity.
  apply H0. left ; reflexivity.
  apply extCKH_Deduction_Theorem. apply IHl.
  apply Id. right ; apply In_singleton.
  intros. apply extCKH_monot with Γ. apply H0 ; auto.
  intros C HC ; left ; auto. auto.
Qed.

Lemma list_disj_Box_obj : forall l Γ,
  extCKH_prv AdAx Γ (list_disj (map Box l) --> ☐ (list_disj l)).
Proof.
induction l ; cbn ; intros.
- apply EFQ.
- eapply MP. eapply MP. apply Ax ; left ; left ; eapply IA5 ; reflexivity.
  eapply MP. apply Ax ; left ; right ; eapply Kb ; reflexivity.
  apply Nec. apply Ax ; left ; left ; eapply IA3 ; reflexivity.
  eapply MP. eapply MP. apply Imp_trans.
  apply IHl. eapply MP. apply Ax ; left ; right ; eapply Kb ; reflexivity.
  apply Nec. apply Ax ; left ; left ; eapply IA4 ; reflexivity.
Qed.

Lemma list_disj_Box : forall l Γ,
  extCKH_prv AdAx Γ (list_disj (map Box l)) ->
  extCKH_prv AdAx Γ (☐ (list_disj l)).
Proof.
intros. eapply MP. apply list_disj_Box_obj. auto.
Qed.

End list_of_disjunctions.






Section list_of_conjunctions.

Fixpoint list_conj (l : list form) :=
match l with
 | nil => Top
 | h :: t => And h (list_conj t)
end.

Lemma list_conj_map_Diam : forall l, (forall A, List.In A l -> exists B, A = ⬦ B) ->
                exists l', l = map Diam l'.
Proof.
induction l ; cbn ; intros ; auto.
- exists [] ; auto.
- destruct (H a) ; auto ; subst.
  destruct (IHl). intros. apply H ; auto. subst.
  exists (x :: x0). cbn ; auto.
Qed.

Lemma forall_list_conj : forall l Γ,
  (forall B, List.In B l -> extCKH_prv AdAx Γ B) ->
  extCKH_prv AdAx Γ (list_conj l).
Proof.
induction l ; cbn ; intros ; auto.
- apply prv_Top.
- eapply MP. eapply MP. eapply MP.
  apply Ax ; left ; left ; eapply IA8 ; reflexivity. apply imp_Id_gen.
  eapply MP. apply Thm_irrel. apply IHl. intros ; auto.
  apply H ; auto.
Qed.

Lemma list_conj_Diam_obj : forall l Γ,
  extCKH_prv AdAx Γ ((⬦ (list_conj l)) --> list_conj (map Diam l)).
Proof.
induction l ; cbn ; intros.
- eapply MP. apply Thm_irrel. apply prv_Top.
- eapply MP. eapply MP. apply Ax ; left ; left ; eapply IA8 ; reflexivity.
  eapply MP. apply Ax ; left ; right ; eapply Kd ; reflexivity.
  apply Nec. apply Ax ; left ; left ; eapply IA6 ; reflexivity.
  eapply MP. eapply MP. apply Imp_trans.
  eapply MP. apply Ax ; left ; right ; eapply Kd ; reflexivity.
  apply Nec. apply Ax ; left ; left ; eapply IA7 ; reflexivity.
  apply IHl.
Qed.

Lemma list_conj_Diam : forall l Γ,
  extCKH_prv AdAx Γ (⬦ (list_conj l)) ->
  extCKH_prv AdAx Γ (list_conj (map Diam l)).
Proof.
intros. eapply MP. apply list_conj_Diam_obj. auto.
Qed.

Lemma prv_list_left_conj : forall l Γ A,
  extCKH_prv AdAx (Union _ Γ (fun x => List.In x l)) A ->
  extCKH_prv AdAx (Union _ Γ (Singleton _ (list_conj l))) A.
Proof.
induction l ; cbn ; intros.
- apply (extCKH_monot _ _ _ H). intros B HB. inversion HB ; subst.
  + left ; auto.
  + inversion H0.
- apply extCKH_comp with (Union _ (Union _ Γ (Singleton _ a)) (Singleton _ (list_conj l))).
  + apply IHl. apply (extCKH_monot _ _ _ H). intros B HB. inversion HB ; subst.
    * left ; left ; auto.
    * inversion H0 ; subst. left ; right ; apply In_singleton. right ; cbn ; auto.
  + intros. inversion H0 ; subst. inversion H1 ; subst. apply Id. left ; auto.
     inversion H2 ; subst. apply extCKH_Detachment_Theorem. apply Ax ; left ; left ; eapply IA6 ; reflexivity.
     inversion H1 ; subst. apply extCKH_Detachment_Theorem. apply Ax ; left ; left ; eapply IA7 ; reflexivity.
Qed.

End list_of_conjunctions.


Section Axioms.

Theorem more_AdAx_more_prv : forall P0 P1, (forall A, P0 A -> P1 A) -> forall Γ A, extCKH_prv P0 Γ A -> extCKH_prv P1 Γ A.
Proof.
intros. induction H0.
- apply Id ; auto.
- apply Ax. firstorder.
- eapply MP. exact IHextCKH_prv1. auto.
- apply Nec. auto.
Qed.

End Axioms.

End theorems_and_meta.





Section Additional_ax.

Lemma list_Box_map_repr : forall l, (forall A : form, List.In A l -> exists B : form, A = ☐ B) ->
      exists l', l = map Box l'.
Proof.
induction l ; cbn ; intros.
- exists [] ; auto.
- destruct (H a) ; auto ; subst. destruct IHl ; auto ; subst.
  exists (x :: x0). cbn ; auto.
Qed.

Lemma list_Diam_map_repr : forall l, (forall A : form, List.In A l -> exists B : form, A = ⬦ B) ->
      exists l', l = map Diam l'.
Proof.
induction l ; cbn ; intros.
- exists [] ; auto.
- destruct (H a) ; auto ; subst. destruct IHl ; auto ; subst.
  exists (x :: x0). cbn ; auto.
Qed.

Variable AdAx : form -> Prop.

Definition AdAxCd := fun x => AdAx x \/ (exists A B, (Cd A B) = x).

Lemma Diam_distrib_list_disj l : (l <> []) -> (* Sufficient, but necessary? *)
  forall Γ, extCKH_prv AdAxCd Γ (⬦ (list_disj l)) -> extCKH_prv AdAxCd Γ (list_disj (map Diam l)).
Proof.
induction l ; cbn ; intros.
- contradiction.
- destruct l ; cbn in * ; auto.
  + eapply MP. apply Ax ; left ; left ; eapply IA3 ; reflexivity.
     eapply MP. 2: exact H0. eapply MP. apply Ax ; left ; right ; eapply Kd ; reflexivity.
     apply Nec. eapply MP. eapply MP. apply Ax ; left ; left ; eapply IA5 ; reflexivity.
     apply imp_Id_gen. apply EFQ.
  + eapply MP. eapply MP. eapply MP. apply Ax ; left ; left ; eapply IA5 ; reflexivity.
     apply Ax ; left ; left ; eapply IA3 ; reflexivity.
     eapply MP. eapply MP. apply Imp_trans. 2: apply Ax ; left ; left ; eapply IA4 ; reflexivity.
     apply extCKH_Deduction_Theorem. apply IHl. intro H1 ; inversion H1.
     apply Id. right ; apply In_singleton. eapply MP. 2: apply H0. apply Ax ; right ; right ; eexists ; eexists ; reflexivity.
Qed.

End Additional_ax.

