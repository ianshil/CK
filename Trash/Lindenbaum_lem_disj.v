Require Import Classical.

Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Lia.
Require Import Ensembles.
Require Import Coq.Logic.Description.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import im_syntax.
Require Import CKH.
Require Import logic.
Require Import properties.
Require Import enum.
Require Import Lindenbaum_disj_trick.


Section Sets_of_forms.

Definition SubTheory (Γ Δ : @Ensemble form) (Incl: Included _ Δ Γ) := forall φ, ((CKH_prv Δ φ) /\ In _ Γ φ) -> In _ Δ φ.

Definition restr_closed Γ Δ :=
  forall φ, CKH_prv Δ φ -> Γ φ -> Δ φ.

Definition prime (Γ : @Ensemble form) :=
  forall φ ψ, Γ (Or φ ψ) -> Γ φ \/ Γ ψ.

Definition quasi_prime (Γ : @Ensemble form) :=
  forall φ ψ, Γ (Or φ ψ) -> ~ ~ (Γ φ \/ Γ ψ).

End Sets_of_forms.




Section Prime.

(* Can probably get a simpler function. *)

Definition choice_form Γ C A1 A2 : Ensemble _ :=
fun x => (In _ Γ x) \/
  ((CKH_prv Γ (Or A1 A2)) /\
    ((~ CKH_prv (Union _ Γ (Singleton _ A1)) C /\ x = A1) \/
     (CKH_prv (Union _ Γ (Singleton _ A1)) C /\ x = A2))).

Definition choice_code Γ C n : Ensemble _ :=
match form_enum n with
      | Or A1 A2 => choice_form Γ C A1 A2
      | _ => Γ
end.


Fixpoint nprime_theory Γ C n :=
match n with
| 0 => Γ
| S m => choice_code (nprime_theory Γ C m) C m
end.

Definition prime_theory Γ C :=
  fun x => (exists n, In _ (nprime_theory Γ C n) x).

End Prime.









Section PrimeProps.

(* A prime theory is an extension of the initial theory. *)

Lemma nprime_theory_extens : forall n Γ C x,
    Γ x -> (nprime_theory Γ C n) x.
Proof.
induction n ; cbn ; intros ; auto.
pose (IHn Γ C x H). unfold choice_code.
destruct (form_enum n) ; subst ; auto.
unfold choice_form. auto.
Qed.

Lemma nprime_theory_extens_le : forall m n Γ C x,
    (nprime_theory Γ C n) x -> (n <= m) -> (nprime_theory Γ C m) x.
Proof.
induction m ; cbn ; intros ; auto.
- inversion H0 ; subst. cbn in H ; auto.
- inversion H0 ; subst ; auto.
  apply IHm in H ; auto. unfold choice_code ; destruct (form_enum m) ; cbn ; auto.
  left ; auto.
Qed.

Lemma prime_theory_extens : forall Γ C x,
    Γ x -> (prime_theory Γ C) x.
Proof.
intros. unfold prime_theory. unfold In. exists 0. auto.
Qed.

(* Each step of the construction preserves relative consistency. *)

Lemma Under_nprime_theory : forall n Γ C,
  ~ CKH_prv Γ C ->
  ~ CKH_prv (nprime_theory Γ C n) C.
Proof.
induction n ; intros ; cbn in * ; auto.
intro. apply (IHn Γ C) ; auto. unfold choice_code in H0.
destruct (form_enum n) ; cbn in * ; auto.
unfold choice_form in * ; cbn in *.
destruct (classic (CKH_prv (nprime_theory Γ C n) (f1 ∨ f2))).
- destruct (classic (CKH_prv (Union form (nprime_theory Γ C n) (Singleton form f1)) C)).
  + eapply MP. eapply MP. eapply MP. apply Ax. left. eapply IA5 ; reflexivity.
     apply CKH_Deduction_Theorem. exact H2.
     apply CKH_Deduction_Theorem. apply (CKH_monot _ _ H0).
     intros D HD. unfold In in *. destruct HD. left ; auto.
     destruct H3. destruct H4. exfalso ; firstorder. destruct H4 ; subst.
     right ; apply In_singleton. auto.
  + exfalso. apply H2. apply (CKH_monot _ _ H0).
     intros D HD. unfold In in *. destruct HD. left ; auto.
     destruct H3. destruct H4. destruct H4 ; subst. right ; apply In_singleton.
     exfalso ; firstorder.
- apply (CKH_monot _ _ H0).
  intros D HD. unfold In in *. destruct HD ; auto. destruct H2 ; exfalso ; auto.
Qed.

(* A prime theory preserves derivability. *)

Lemma der_nprime_theory_mprime_theory_le : forall n m Γ C A,
  (CKH_prv (nprime_theory Γ C n) A) -> (n <= m) ->
    (CKH_prv (nprime_theory Γ C m) A).
Proof.
intros.
apply (CKH_monot _ _ H). intros D HD.
apply nprime_theory_extens_le with n ; auto.
Qed.

Lemma der_prime_theory_nprime_theory : forall Γ C A, CKH_prv (prime_theory Γ C) A ->
                                        exists n, CKH_prv (nprime_theory Γ C n) A.
Proof.
intros Γ C A D. remember (prime_theory Γ C) as X. revert Γ C HeqX.
induction D ; cbn ; intros ; subst.
- destruct H as (n & Hn). exists n ; apply Id ; auto.
- exists 0 ; apply Ax ; auto.
- destruct (IHD2 Γ0 C) ; auto. destruct (IHD1 Γ0 C) ; auto.
  exists (max x x0). eapply MP. apply der_nprime_theory_mprime_theory_le with x0.
  exact H0. lia. apply der_nprime_theory_mprime_theory_le with x. exact H. lia.
- exists 0. apply Nec ; auto.
Qed.

(* A prime theory is prime. *)

Lemma primeness_Lind_der : forall Γ C, ~ CKH_prv Γ C ->
  (forall A1 A2, CKH_prv (prime_theory Γ C) (Or A1 A2) ->
  ((prime_theory Γ C) A1 \/ (prime_theory Γ C) A2)).
Proof.
intros.

(* There is a n s.t. (nprime_theory Γ C n) derives the disjunction. *)
destruct (der_prime_theory_nprime_theory _ _ _ H0) as (x & Hx).

(* There must be m and l s.t.  n < m and (S m) is the encoding of (Or A1 (Or A2 (Bot x l)))
   and the latter is derived by (nprime_theory Γ C m). *)
assert (exists l m, (form_enum m = (Or A1 (Or A2 (mult_disj l (Bot))))) /\
(x <= m)).
{ pose (too_many_disj0 x A1 A2). destruct e. destruct H1. exists x1.
  exists x0. auto. }
destruct H1. destruct H1. destruct H1.
assert (J3: CKH_prv (nprime_theory Γ C x1) (Or A1 (Or A2 (mult_disj x0 (Bot))))).
apply CKH_monot with (Γ1:=nprime_theory Γ C x1) in Hx.
eapply MP. eapply MP. eapply MP. apply Ax ; left ; eapply IA5 ; reflexivity.
apply Ax ; left ; eapply IA3 ; reflexivity. eapply MP. eapply MP. apply Imp_trans.
apply Ax ; left ; eapply IA3 ; reflexivity. apply Ax ; left ; eapply IA4 ; reflexivity.
auto.
intro. intros. cbn in H3. apply nprime_theory_extens_le with (n:=x) ; auto.

(* Then (nprime_theory Γ C (m)) must take A1 or (Or A2 (Bot x l)). *)
assert (In _ (nprime_theory Γ C (S x1)) A1 \/
((CKH_prv (Union _ (nprime_theory Γ C x1) (Singleton _ A1)) C))
  /\ (nprime_theory Γ C (S x1)) (Or A2 (mult_disj x0 (Bot)))).
cbn. unfold choice_code. rewrite H1.
unfold choice_form. cbn.
(* LEM *) destruct (classic (CKH_prv (Union _ (nprime_theory Γ C x1) (Singleton _ A1)) C)).
right. unfold In in * ; cbn in *. split ; auto.
left. unfold In in *. right. repeat split ; auto.
destruct H3.

(* If it takes A1, then we are done as A1 is in (prime_theory Γ C). *)
left. exists (S x1) ; auto.

(* If it takes (Or A2 (Bot x l)) we need more work. *)
right. destruct H3.

(* Note that (nprime_theory Γ C (S x1)) derives A2. *)
assert (CKH_prv (nprime_theory Γ C (S x1)) A2).
apply der_mult_disj_Bot with (n:= x0). apply Id. auto.

(* There is a k and o s.t. S (x1) < k and (S k) is the encoding for (Or A2 (mult_disj o (Bot))). *)
assert (exists k o, (form_enum k = (Or A2 (mult_disj o (Bot)))) /\
((S x1) <= k)). apply too_many_disj1.
destruct H6. destruct H6. destruct H6.

(* Then (nprime_theory Γ C (S k)) derives (Or A2 (mult_disj o Bot)) as it derives A2. *)
assert (J4: CKH_prv (nprime_theory Γ C x2) (Or A2 (mult_disj x3 (Bot)))).
eapply MP. apply Ax ; left ; eapply IA3 ; reflexivity.
apply CKH_monot with (Γ1:=nprime_theory Γ C x2) in H5. auto.
intro. intros. apply nprime_theory_extens_le with (n:=(S x1)) ; auto ; lia.

(* So this theory has to take A2 and then we are done as A2 is in prime_theory Γ Δ. *)
assert (In _ (nprime_theory Γ C (S x2)) A2).
cbn. unfold choice_code. rewrite H6. unfold choice_form. cbn. unfold In. right. split ; auto.
left. split ; auto. intro.
apply Under_nprime_theory with (n:=x2) (Γ:=Γ) (C:=C) ; auto.
eapply MP. eapply MP. eapply MP. apply Ax ; left ; eapply IA5 ; reflexivity.
apply CKH_Deduction_Theorem ; exact H8.
apply CKH_monot with (Γ1:=Union _ (nprime_theory Γ C x2) (Singleton _ A1)) in H3 ; auto ; cbn.
apply CKH_Deduction_Theorem ; exact H3.
intro. intros. inversion H9. subst. left.
apply nprime_theory_extens_le with (n:=x1) ; auto ; lia.
subst. inversion H10. right. apply In_singleton.
apply CKH_monot with (Γ1:=nprime_theory Γ C x2) in Hx ; auto.
apply comm_Or. auto. intro. intros. apply nprime_theory_extens_le with (n:=x) ; auto ; lia.

exists (S x2) ; auto.
Qed.

Lemma primeness_Lind: forall Γ C, (CKH_prv Γ C -> False) ->
  (forall A1 A2, In _ (prime_theory Γ C) (Or A1 A2) -> ((In _ (prime_theory Γ C) A1) \/ (In _ (prime_theory Γ C) A2))).
Proof.
intros. apply primeness_Lind_der ; auto. apply Id ; auto.
Qed.

Lemma list_primeness_Lind : forall Γ C, (CKH_prv Γ C -> False) ->
  (forall x, In _ (prime_theory Γ C) (list_disj x) -> ((In _ (prime_theory Γ C) (Bot)) \/ (exists A, List.In A x /\ (In _ (prime_theory Γ C) A)))).
Proof.
intros. induction x.
- cbn in H0. left. auto.
- cbn. cbn in H0. apply primeness_Lind in H0. destruct H0. right.
  exists a. auto. 2: auto. apply IHx in H0. destruct H0. left. auto.
  right. destruct H0. destruct H0. clear IHx. exists x0. auto.
Qed.


(* A prime theory is closed under derivation. *)

Lemma closeder_Lind: forall Γ C, ~ CKH_prv Γ C ->
  (forall A, CKH_prv (prime_theory Γ C) A -> (prime_theory Γ C) A).
Proof.
intros. assert (CKH_prv (prime_theory Γ C) (Or A A)). eapply MP.
apply Ax ; left ; eapply IA3 ; reflexivity. auto.
apply primeness_Lind_der in H1 ; auto. destruct H1 ; auto.
Qed.

(* A prime pair is consistent, if the initial set is. *)

Lemma Consist_nprime_theory : forall n Γ C, ~ CKH_prv Γ C ->
  ~ CKH_prv (nprime_theory Γ C n) Bot.
Proof.
intros. intro. pose (Under_nprime_theory n Γ C H).
apply n0. eapply MP. apply EFQ. auto.
Qed.

Lemma Consist_prime_theory : forall Γ C, ~ CKH_prv Γ C ->
  ~ CKH_prv (prime_theory Γ C) Bot.
Proof.
intros. intro. apply closeder_Lind in H0 ; auto. unfold prime_theory in H0.
unfold In in H0. destruct H0. apply Consist_nprime_theory with (Γ:=Γ) (C:=C) (n:=x) ; auto.
apply Id ; auto.
Qed.

(* Need to define the closure in the syntax. *)

Lemma Lindenbaum Γ Δ ψ :
  In _ (Clos Γ) ψ ->
  Included _ Δ (Clos Γ) ->
  ~ CKH_prv (Δ, ψ) ->
  exists Δm, Included _ Δ Δm
           /\ Included _ Δm (Clos Γ)
           /\ restr_closed (Clos Γ) Δm
           /\ quasi_prime Δm
           /\ ~ CKH_prv (Δm, ψ).
Proof.
intros.
exists (Lind_theory (Clos Γ) Δ ψ).
repeat split.
- intro. apply Lind_theory_extens.
- apply incl_Lind_theory ; auto.
- apply restr_closeder_Lind_theory ; auto.
- pose quasi_prime_Lind_theory ; auto.
- intro. apply Under_Lind_theory with (Γ:=(Clos Γ)) in H1 ; auto.
Qed.


