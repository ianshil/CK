Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH.

Lemma subst_Ax : forall A f, (Axioms A) -> (Axioms (subst f A)).
Proof.
intros A f Ax. destruct Ax.
+ destruct H ; left ; subst ; cbn ;
   [ eapply IA1 ; reflexivity | eapply IA2 ; reflexivity | eapply IA3 ; reflexivity |
     eapply IA4 ; reflexivity | eapply IA5 ; reflexivity | eapply IA6 ; reflexivity |
     eapply IA7 ; reflexivity | eapply IA8 ; reflexivity | eapply IA9 ; reflexivity].
+ destruct H ; right ; subst ; cbn ; [ eapply MAK1 ; reflexivity | eapply MAK2 ; reflexivity].
Qed.

Theorem CKH_monot : forall Γ A,
          CKH_prv Γ A ->
          forall Γ1, (Included _ Γ Γ1) ->
          CKH_prv Γ1 A.
Proof.
intros Γ A D0. induction D0 ; intros Γ1 incl.
(* Id *)
- apply Id ; auto.
(* Ax *)
- apply Ax ; auto.
(* MP *)
- apply MP with A ; auto.
(* Nec *)
- apply Nec ; auto.
Qed.

Theorem CKH_comp : forall Γ A,
          CKH_prv Γ A ->
          forall Γ', (forall B, Γ B -> CKH_prv Γ' B) ->
          CKH_prv Γ' A.
Proof.
intros Γ A D0. induction D0 ; intros Γ' derall ; auto.
(* Ax *)
- apply Ax ; auto.
(* MP *)
- apply MP with A ; auto.
(* Nec *)
- apply Nec ; auto.
Qed.

Theorem CKH_struct : forall Γ A,
          CKH_prv Γ A ->
          forall (f : nat -> form),
          CKH_prv (fun y => exists B, Γ B /\ y = (subst f B)) (subst f A).
Proof.
intros Γ A D0. induction D0 ; intros f.
(* Id *)
- apply Id ; unfold In ; exists A ; auto.
(* Ax *)
- apply Ax ; apply subst_Ax ; auto.
(* MP *)
- cbn in *. apply MP with (subst f A) ; auto.
(* Nec *)
- cbn in * ; subst. apply Nec ; auto.
  apply CKH_monot with (fun y : form => exists B : form, Empty_set form B /\ y = subst f B) ; auto.
  intros C HC ; destruct HC as (D & H0 & H1) ; inversion H0.
Qed.

Theorem CKH_finite : forall Γ A,
          CKH_prv Γ A ->
          exists Fin, Included _ Fin Γ /\
                           CKH_prv Fin A /\
                           exists l, forall A, (Fin A -> List.In A l) /\ (List.In A l -> Fin A).
Proof.
intros Γ A D0. induction D0.
(* Id *)
- exists (fun x => x = A). repeat split ; auto.
  + intros B HB ; inversion HB ; auto.
  + apply Id ; unfold In ; auto.
  + exists [A]. intro B. split ; intro HB ; subst. apply in_eq. inversion HB ; auto.
     inversion H0.
(* Ax *)
- exists (Empty_set _). repeat split ; auto.
  + intros B HB ; inversion HB.
  + apply Ax ; auto.
  + exists []. intro B. split ; intro HB ; inversion HB.
(* MP *)
- destruct IHD0_1 as (Left & HR0 & HR1 & (l0 & Hl0)).
  destruct IHD0_2 as (Right & HL0 & HL1 & (l1 & Hl1)).
  exists (Union _ Left Right). repeat split ; auto.
  + intros C HC ; inversion HC ; subst ; auto.
  + apply MP with A.
     apply CKH_monot with Left ; auto. intros C HC ; apply Union_introl ; auto.
     apply CKH_monot with Right ; auto. intros C HC ; apply Union_intror ; auto.
  + exists (l0 ++ l1). intro C. split ; intro HC. apply in_or_app ; inversion HC ; subst ; firstorder.
     destruct (in_app_or _ _ _ HC). apply Union_introl ; firstorder. apply Union_intror ; firstorder.
(* Nec *)
- exists (Empty_set _). repeat split ; auto.
  + intros C HC ; inversion HC.
  + apply Nec ; auto.
  + exists []. intro C. split ; intro HC ; inversion HC.
Qed.
