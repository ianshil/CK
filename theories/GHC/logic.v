From Stdlib Require Import List.
Export ListNotations.
From Stdlib Require Import Arith.
From Stdlib Require Import Ensembles.

Require Import im_syntax.
Require Import CKH.

Section logic_props.

Variable AdAx : form -> Prop.
Hypothesis AdAx_subst_clos : forall A, AdAx A -> forall f, AdAx (subst f A).

Lemma subst_Ax : forall A f, (Axioms A) -> (Axioms (subst f A)).
Proof.
intros A f Ax. destruct Ax.
+ destruct H ; left ; subst ; cbn ;
   [ eapply IA1 ; reflexivity | eapply IA2 ; reflexivity | eapply IA3 ; reflexivity |
     eapply IA4 ; reflexivity | eapply IA5 ; reflexivity | eapply IA6 ; reflexivity |
     eapply IA7 ; reflexivity | eapply IA8 ; reflexivity | eapply IA9 ; reflexivity].
+ destruct H ; right ; subst ; cbn ; [ eapply Kb ; reflexivity | eapply Kd ; reflexivity].
Qed.

Theorem extCKH_monot : forall Γ A,
          extCKH_prv AdAx Γ A ->
          forall Γ1, (Included _ Γ Γ1) ->
          extCKH_prv AdAx Γ1 A.
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

Theorem extCKH_comp : forall Γ A,
          extCKH_prv AdAx Γ A ->
          forall Γ', (forall B, Γ B -> extCKH_prv AdAx Γ' B) ->
          extCKH_prv AdAx Γ' A.
Proof.
intros Γ A D0. induction D0 ; intros Γ' derall ; auto.
(* Ax *)
- apply Ax ; auto.
(* MP *)
- apply MP with A ; auto.
(* Nec *)
- apply Nec ; auto.
Qed.

Theorem extCKH_struct : forall Γ A,
          extCKH_prv AdAx Γ A ->
          forall (f : nat -> form),
          extCKH_prv AdAx (fun y => exists B, Γ B /\ y = (subst f B)) (subst f A).
Proof.
intros Γ A D0. induction D0 ; intros f.
(* Id *)
- apply Id ; unfold In ; exists A ; auto.
(* Ax *)
- apply Ax. destruct H.
  + left ; apply subst_Ax ; auto.
  + right ; apply AdAx_subst_clos ; auto.
(* MP *)
- cbn in *. apply MP with (subst f A) ; auto.
(* Nec *)
- cbn in * ; subst. apply Nec ; auto.
  apply extCKH_monot with (fun y : form => exists B : form, Empty_set form B /\ y = subst f B) ; auto.
  intros C HC ; destruct HC as (D & H0 & H1) ; inversion H0.
Qed.

Theorem extCKH_finite : forall Γ A,
          extCKH_prv AdAx Γ A ->
          exists Fin, Included _ Fin Γ /\
                           extCKH_prv AdAx Fin A /\
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
     apply extCKH_monot with Left ; auto. intros C HC ; apply Union_introl ; auto.
     apply extCKH_monot with Right ; auto. intros C HC ; apply Union_intror ; auto.
  + exists (l0 ++ l1). intro C. split ; intro HC. apply in_or_app ; inversion HC ; subst ; firstorder.
     destruct (in_app_or _ _ _ HC). apply Union_introl ; firstorder. apply Union_intror ; firstorder.
(* Nec *)
- exists (Empty_set _). repeat split ; auto.
  + intros C HC ; inversion HC.
  + apply Nec ; auto.
  + exists []. intro C. split ; intro HC ; inversion HC.
Qed.

End logic_props.
