Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Lia.

Require Import Coq.Logic.Description.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import Ensembles.
Require Import im_syntax.
Require Import CKH.
Require Import logic.
Require Import properties.
Require Import remove_list.
Require Import enum.

(* ------------------------------------------------------------------------------------------------------------------------------------ *)

(* Random lemmas. *)

Lemma nat_remove_le_length : forall l (n : nat), length (remove Nat.eq_dec n l) <= length l.
Proof.
induction l.
- intros. cbn. reflexivity.
- intros. cbn. destruct (Nat.eq_dec n a).
  * subst. apply le_S. apply IHl.
  * cbn. apply le_n_S. apply IHl.
Qed.

Lemma nat_remove_In_smaller_length : forall (l : list nat) (n : nat),
       List.In n l -> length (remove Nat.eq_dec n l) < length l.
Proof.
induction l.
- intros. inversion H.
- intros. cbn. destruct (Nat.eq_dec n a).
  * subst. unfold lt. apply le_n_S. apply nat_remove_le_length.
  * cbn. inversion H ; subst. exfalso ; apply n0 ; auto.
    apply IHl in H0 ; lia.
Qed.

Lemma max_of_list : forall (l : list nat), ((l = []) -> False) -> (exists n, (List.In n l) /\
            (forall m, List.In m l -> m <= n)).
Proof.
induction l.
- cbn. intros. exfalso. apply H. auto.
- intros. destruct l.
  * exists a. split. apply in_eq. intros. inversion H0. subst. auto. inversion H1.
  * assert (n :: l = [] -> False). intro. inversion H0. apply IHl in H0.
    destruct H0. destruct H0. inversion H0.
    + subst. exists (Nat.max a x). split. pose (Nat.max_dec a x).
      destruct s. rewrite e. apply in_eq. rewrite e. apply in_cons. apply in_eq.
      intros. inversion H2. lia. pose (H1 m). apply l0 in H3. lia.
    + exists (Nat.max a x). split. pose (Nat.max_dec a x).
      destruct s. rewrite e. apply in_eq. rewrite e. apply in_cons. apply in_cons. auto.
      intros. inversion H3. lia. pose (H1 m). apply l0 in H4. lia.
Qed.

Lemma always_add_a_nat : forall (l : list nat), (NoDup l) -> (exists n, (NoDup (n :: l))).
Proof.
intros. destruct l.
- exists 0. apply NoDup_cons ; auto ; apply NoDup_nil.
- assert (J1: (n :: l = [] -> False) ). intro. inversion H0.
  pose (max_of_list (n :: l) J1). destruct e. destruct H0. exists (S x).
  apply NoDup_cons. intro. apply H1 in H2. lia. auto.
Qed.

Lemma no_list_all_nat : (exists (l : list nat), (NoDup l) /\ (forall (n : nat), List.In n l)) -> False.
Proof.
intros. destruct H. destruct H. pose (always_add_a_nat x H). destruct e.
assert (incl (x0 :: x) x). intro. intros. inversion H2. subst. pose (H0 a). auto.
auto. pose (@NoDup_incl_length nat (x0 :: x) x H1 H2). cbn in l. lia.
Qed.

Lemma list_all_pred_nat : forall n, exists l, (NoDup l) /\ (forall m, (m <= n) <-> List.In m l).
Proof.
induction n. exists [0]. split. apply NoDup_cons ; auto ; apply NoDup_nil.
intros. split ; intro. inversion H. subst. apply in_eq.
inversion H. subst. auto. inversion H0. destruct IHn. destruct H. exists ((S n) :: x).
intros. split. apply NoDup_cons. intro. apply H0 in H1. lia. auto.
split ; intros. inversion H1. subst. apply in_eq. subst. apply in_cons.
apply H0. auto. inversion H1. subst. auto. apply H0 in H2. lia.
Qed.


(* ------------------------------------------------------------------------------------------------------------------------------------ *)

(* Multiple disjunctions lemmas. *)

Fixpoint mult_disj n (A : form) : form :=
match n with
  | 0 => A
  | S m => Or A (mult_disj m A)
  end.

Lemma der_mult_disj_Bot : forall n Γ A,
  CKH_prv Γ (Or A (mult_disj n (Bot))) -> CKH_prv Γ (A).
Proof.
induction n.
- cbn. intros. apply absorp_Or1. auto.
- cbn. intros. eapply MP. eapply MP. eapply MP. apply Ax ; left ; eapply IA5 ; reflexivity.
  apply imp_Id_gen. eapply MP. eapply MP. apply Imp_trans.
  apply CKH_Deduction_Theorem ; auto. apply IHn. apply Id ; right ; apply In_singleton.
  apply EFQ. auto.
Qed.

Lemma mult_disj_Id : forall x y, (mult_disj x (Bot) = mult_disj y (Bot)) -> x = y.
Proof.
induction x.
- intros. cbn in H. destruct y. auto. cbn in H. destruct y. cbn in H. inversion H.
  inversion H.
- induction y.
  * intros. cbn in H. inversion H.
  * intros. cbn in H. inversion H. apply IHx in H1. auto.
Qed.

Lemma mult_disj_dec0 : forall C,
  (exists g, C = (mult_disj g (Bot))) \/ ((exists g, C = (mult_disj g (Bot))) -> False).
Proof.
induction C ; cbn ; auto.
1,3,5-7: right ; intros ; destruct H ; inversion H ; destruct x ; inversion H.
- left. exists 0 ; cbn ; auto.
- destruct IHC1.
  + destruct H ; subst. destruct IHC2.
    * destruct H ; subst. destruct x ; cbn.
      { left. exists (S x0) ; cbn ; auto. }
      { right. intros. destruct H. destruct x1 ; cbn in H.
        inversion H. inversion H. }
    * right. intros. destruct H0. destruct x0 ; cbn in *. inversion H0.
      destruct x ; cbn in *. inversion H0 ; subst. apply H ; exists x0 ; auto.
      inversion H0.
  + right. intro. destruct H0. destruct x ; cbn in *. inversion H0.
     inversion H0 ; subst. apply H. exists 0 ; cbn ; auto.
Qed.

Lemma mult_disj_dec1 : forall C B,
  (exists g, C = (Or B (mult_disj g (Bot)))) \/ ((exists g, C = (Or B (mult_disj g (Bot)))) -> False).
Proof.
destruct C ; cbn ; auto. 
1-3,5-7: right ; intros ; destruct H ; inversion H. 
intros. destruct (eq_dec_form C1 B) ; subst.
2: right ; intro ; destruct H ; inversion H ; auto.
destruct (mult_disj_dec0 C2).
destruct H ; subst. left ; exists x ; auto.
right ; intro. destruct H0. inversion H0 ; subst.
apply H. exists x ; auto.
Qed.

Lemma mult_disj_dec : forall C A B,
  (exists g, C = (Or A (Or B (mult_disj g (Bot))))) \/ ((exists g, C = (Or A (Or B (mult_disj g (Bot))))) -> False).
Proof.
destruct C ; cbn ; auto.
1-3,5-7: right ; intros ; destruct H ; inversion H.
intros. destruct (eq_dec_form C1 A) ; subst. 2: right ; intro ; destruct H ; inversion H ; auto.
destruct (mult_disj_dec1 C2 B) ; subst. destruct H ; subst. left. exists x ; auto.
right;  intro. destruct H0 ; subst. inversion H0 ; subst. apply H. exists x ; auto.
Qed.

Lemma too_many_disj00 : forall (n : nat) A B,
((exists (m k : nat), (m <= n) /\ (form_enum m = (Or A (Or B (mult_disj k (Bot)))))) -> False)
\/
  (exists (m max : nat), (form_enum m = (Or A (Or B (mult_disj max (Bot)))) /\ (m <= n))
  /\
  (forall (o p : nat), ((form_enum p = (Or A (Or B (mult_disj o (Bot)))) /\ (p <= n)) ->
        o <= max))).
Proof.
induction n.
- intros. destruct (mult_disj_dec (form_enum 0) A B).
    * destruct H. right. exists 0. exists x. repeat split ; auto.
      subst. auto. intros. destruct H0. inversion H1. subst. clear H1.
      rewrite H in H0. inversion H0. apply mult_disj_Id in H2. lia.
    * left. intro. destruct H0. destruct H0. destruct H0. inversion H0. subst.
      apply H. exists x0. auto.
- intros. destruct (mult_disj_dec (form_enum (S n)) A B).
    * destruct H. subst. right. pose (IHn A B). destruct o.
      { clear IHn. exists (S n). exists x. repeat split ; auto.
        intros. destruct H1. inversion H2 ; subst.
        rewrite H in H1. inversion H1. apply mult_disj_Id in H4 ; subst.
        lia. subst. exfalso. apply H0. exists p. exists o. split ; auto. }
      { clear IHn. destruct H0. destruct H0. destruct H0. destruct H0.
        pose (Nat.max_dec x1 x). destruct s.
        - exists x0. exists x1. repeat split ; auto. intros. destruct H3.
          inversion H4. subst. rewrite H in H3. inversion H3. subst.
          apply mult_disj_Id in H6. lia. subst. apply H1 with (p:=p).
          split ; auto.
        - exists (S n). exists x. repeat split ; auto. intros. destruct H3.
          inversion H4. subst. rewrite H in H3. inversion H3.
          apply mult_disj_Id in H6. lia. subst. pose (H1 o p). destruct l.
          split ; auto. lia. lia. }
    * pose (IHn A B). destruct o.
      { left. intro. clear IHn. destruct H1. destruct H1. destruct H1. subst.
        inversion H1. subst. apply H. exists x0. auto.
        subst. apply H0. exists x. exists x0. split ; auto. }
      { right. clear IHn. destruct H0. destruct H0. destruct H0. destruct H0.
        exists x. exists x0. repeat split ; auto. intros. destruct H3. inversion H4.
        subst. exfalso. apply H. exists o ; auto.
        subst. apply H1 with (p:=p). split ; auto. }
Qed.

Lemma too_many_disj0 : forall (n : nat) A B,
 (exists (m k : nat), (form_enum m =  (Or A (Or B (mult_disj k (Bot)))) /\ (n <= m))).
Proof.
intros.
pose (too_many_disj00 n A B). destruct o.
- exists (form_index (Or A (Or B (mult_disj 0 (Bot))))). exists 0.
  split. simpl (mult_disj 0 (Bot)). apply form_enum_index.
  destruct (Nat.le_decidable n (form_index (Or A (Or B (Bot))))) ; auto.
  exfalso. assert ((form_index (Or A (Or B (Bot)))) < n). lia.
  apply H. exists (form_index (Or A (Or B (Bot)))). exists 0. cbn.
  split ; auto. lia. apply form_enum_index.
- destruct H. destruct H. destruct H. destruct H.
  exists (form_index (Or A (Or B (mult_disj (S x0) (Bot))))).
  exists (S x0). split. simpl (mult_disj (S x0) (Bot)). apply form_enum_index.
  destruct (Nat.le_decidable n ((form_index (Or A (Or B (Or (Bot) (mult_disj x0 (Bot)))))))) ; auto.
  assert ((form_index (Or A (Or B (Or (Bot) (mult_disj x0 (Bot)))))) <= n). lia.
  clear H2. pose (H0 (S x0) (form_index (Or A (Or B (Or (Bot) (mult_disj x0 (Bot))))))).
  assert (form_enum (form_index (Or A (Or B (Or (Bot) (mult_disj x0 (Bot)))))) =  (Or A (Or B (mult_disj (S x0) (Bot)))) /\
  form_index (Or A (Or B (Or (Bot) (mult_disj x0 (Bot))))) <= n). split.
  cbn. apply form_enum_index. lia. apply l in H2. exfalso. lia.
Qed.

Lemma too_many_disj10 :forall (n : nat) A,
((exists (m k : nat), (m <= n) /\ (form_enum m =  (Or A (mult_disj k (Bot))))) -> False)
\/
  (exists (m max : nat), (form_enum m =  (Or A (mult_disj max (Bot))) /\ (m <= n))
  /\
  (forall (o p : nat), ((form_enum p =  (Or A (mult_disj o (Bot))) /\ (p <= n)) ->
        o <= max))).
Proof.
induction n.
- intros. destruct (mult_disj_dec1 (form_enum 0) A).
    * destruct H. right. exists 0. exists x. repeat split ; auto.
      intros. destruct H0. inversion H1. subst. clear H1.
      rewrite H0 in H. inversion H. apply mult_disj_Id in H2. lia.
    * left. intro. destruct H0. destruct H0. destruct H0. inversion H0. subst.
      apply H. exists x0. auto.
- intros. destruct (mult_disj_dec1 (form_enum (S n)) A).
    * destruct H. subst. right. pose (IHn A). destruct o.
      { clear IHn. exists (S n). exists x. repeat split ; auto.
        intros. destruct H1. inversion H2. subst. rewrite H in H1.
        inversion H1. apply mult_disj_Id in H4. lia. subst. exfalso.
        apply H0. exists p. exists o. split ; auto. }
      { clear IHn. destruct H0. destruct H0. destruct H0. destruct H0.
        pose (Nat.max_dec x1 x). destruct s.
        - exists x0. exists x1. repeat split ; auto. intros. destruct H3.
          inversion H4. subst. rewrite H in H3. inversion H3. subst.
          apply mult_disj_Id in H6. lia. subst. apply H1 with (p:=p).
          split ; auto.
        - exists (S n). exists x. repeat split ; auto. intros. destruct H3.
          inversion H4. subst. rewrite H in H3. inversion H3.
          apply mult_disj_Id in H6. lia. subst. pose (H1 o p). destruct l.
          split ; auto. lia. lia. }
    * pose (IHn A). destruct o.
      { left. intro. clear IHn. destruct H1. destruct H1. destruct H1. subst.
        inversion H1. subst. apply H.
        exists x0. auto. subst. apply H0. exists x. exists x0. split ; auto. }
      { right. clear IHn. destruct H0. destruct H0. destruct H0. destruct H0.
        exists x. exists x0. repeat split ; auto. intros. destruct H3. inversion H4.
        subst. exfalso. apply H. exists o ; auto.
        subst. apply H1 with (p:=p). split ; auto. }
Qed.

Lemma too_many_disj1 : forall (n : nat) A,
 (exists (m k : nat), (form_enum m =  (Or A (mult_disj k (Bot))) /\ (n <= m))).
Proof.
intros.
pose (too_many_disj10 n A). destruct o.
- exists ((form_index (Or A (mult_disj 0 (Bot))))). exists 0.
  split. simpl ((mult_disj 0 (Bot))). apply form_enum_index.
  destruct (Nat.le_decidable n ((form_index (Or A (Bot))))) ; auto.
  exfalso. assert ((form_index (Or A (Bot))) < n). lia.
  apply H. exists (form_index (Or A (Bot))). exists 0. cbn.
  split ; auto. lia. apply form_enum_index.
- destruct H. destruct H. destruct H. destruct H.
  exists ((form_index (Or A (mult_disj (S x0) (Bot))))).
  exists (S x0). split. simpl (mult_disj (S x0) (Bot)). apply form_enum_index.
  destruct (Nat.le_decidable n ((form_index (Or A (Or (Bot) (mult_disj x0 (Bot))))))) ; auto.
  assert ((form_index (Or A (Or (Bot) (mult_disj x0 (Bot))))) <= n). lia.
  clear H2. pose (H0 (S x0) (form_index (Or A (Or (Bot) (mult_disj x0 (Bot)))))).
  assert (form_enum (form_index (Or A (Or (Bot) (mult_disj x0 (Bot))))) =  (Or A (mult_disj (S x0) (Bot))) /\
  form_index (Or A (Or (Bot) (mult_disj x0 (Bot)))) <= n). split.
  cbn. apply form_enum_index. lia. apply l in H2. exfalso. lia.
Qed.





(* ------------------------------------------------------------------------------------------------------------------------------------ *)

(* List of disjunctions. *)

Fixpoint list_disj (l : list form) :=
match l with
 | nil => Bot
 | h :: t => Or h (list_disj t)
end.

Lemma Id_list_disj : forall Γ l0 l1,
  CKH_prv Γ (list_disj l0 --> list_disj (l0 ++ l1)).
Proof.
induction l0 ; intros.
- cbn. apply EFQ.
- cbn. apply monotL_Or. apply IHl0.
Qed.

Lemma list_disj_app : forall l0 Γ A l1,
  CKH_prv Γ (A --> list_disj (l0 ++ l1)) -> CKH_prv Γ (A --> (Or (list_disj l0) (list_disj l1))).
Proof.
induction l0.
- cbn. intros. eapply MP. eapply MP. apply Imp_trans. exact H. apply Ax ; left ; eapply IA4 ; reflexivity.
- cbn. intros. eapply MP. eapply MP. apply Imp_trans. exact H. eapply MP. eapply MP.
  apply Imp_trans. apply monotL_Or. apply IHl0. apply imp_Id_gen. eapply MP.
  eapply MP. apply Ax ; left ; eapply IA5 ; reflexivity. eapply MP. eapply MP. apply Imp_trans.
  apply Ax ; left ; eapply IA3 ; reflexivity. apply Ax ; left ; eapply IA3 ; reflexivity.
  apply monotR_Or. apply Ax ; left ; eapply IA4 ; reflexivity.
Qed.

Lemma list_disj_app0 : forall l0 Γ A l1,
  CKH_prv Γ (A --> (Or (list_disj l0) (list_disj l1))) -> CKH_prv Γ (A --> list_disj (l0 ++ l1)).
Proof.
induction l0.
- cbn. intros. eapply MP. eapply MP. apply Imp_trans. exact H. eapply MP.
  eapply MP. apply Ax ; left ; eapply IA5 ; reflexivity. apply EFQ. apply imp_Id_gen.
- cbn. intros. eapply MP. eapply MP. apply Imp_trans. exact H. eapply MP.
  eapply MP. apply Imp_trans. eapply MP. eapply MP. apply Ax ; left ; eapply IA5 ; reflexivity.
  apply monotL_Or. apply Ax ; left ; eapply IA3 ; reflexivity. eapply MP. eapply MP. apply Imp_trans.
  apply Ax ; left ; eapply IA4 ; reflexivity. apply Ax ; left ; eapply IA4 ; reflexivity.
  apply monotL_Or. apply IHl0. apply imp_Id_gen.
Qed.

Lemma list_disj_remove_app : forall l0 l1 Γ A,
CKH_prv Γ (list_disj (l0 ++ remove_list l0 l1) --> Or A (list_disj (l0 ++ remove eq_dec_form A (remove_list l0 l1)))).
Proof.
induction l0.
- cbn. intros. apply remove_disj.
- cbn. intros. eapply MP. eapply MP. apply Imp_trans.
  apply monotL_Or. eapply MP. eapply MP. apply Imp_trans.
  eapply MP. eapply MP. apply Imp_trans. eapply MP. eapply MP. apply Imp_trans.
  apply list_disj_app. apply imp_Id_gen. apply monotL_Or. apply remove_disj.
  eapply MP. eapply MP. apply Ax ; left ; eapply IA5 ; reflexivity. eapply MP. eapply MP.
  apply Imp_trans. apply Ax ; left ; eapply IA3 ; reflexivity. apply Ax ; left ; eapply IA4 ; reflexivity.
  apply monotL_Or. apply Ax ; left ; eapply IA4 ; reflexivity. apply monotL_Or. apply list_disj_app0.
  apply imp_Id_gen. eapply MP. eapply MP. apply Ax ; left ; eapply IA5 ; reflexivity.
  eapply MP. eapply MP. apply Imp_trans. apply Ax ; left ; eapply IA3 ; reflexivity.
  apply Ax ; left ; eapply IA4 ; reflexivity. apply monotL_Or. apply Ax ; left ; eapply IA4 ; reflexivity. 
Qed.

Lemma Id_list_disj_remove : forall Γ l0 l1,
  CKH_prv Γ (list_disj l1 --> list_disj (l0 ++ remove_list l0 l1)).
Proof.
induction l0.
- intros. cbn. apply imp_Id_gen.
- cbn. intros. eapply MP. eapply MP. apply Imp_trans. apply IHl0.
  apply list_disj_remove_app.
Qed.

Lemma der_list_disj_remove1 : forall Γ A l0 l1,
    (CKH_prv Γ (A --> list_disj l0)) ->
    (CKH_prv Γ (A --> list_disj (l0 ++ remove_list l0 l1))).
Proof.
intros Γ A. induction l0.
- cbn. intros. eapply MP. eapply MP. apply Imp_trans. exact H. apply EFQ.
- intros. cbn in *. eapply MP. eapply MP. apply Imp_trans.
  exact H. apply monotL_Or. apply Id_list_disj.
Qed.

Lemma der_list_disj_remove2 : forall Γ A l0 l1,
    (CKH_prv Γ (A --> list_disj l1)) ->
    (CKH_prv Γ (A --> list_disj (l0 ++ remove_list l0 l1))).
Proof.
intros. eapply MP. eapply MP. apply Imp_trans. exact H.
eapply MP. eapply MP. apply Imp_trans. apply Id_list_disj_remove.
apply imp_Id_gen.
Qed.
