Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.

Section general_seg_completeness.

Axiom LEM : forall P, P \/ ~P.

(* We first create segments of our canonical model. They will act
    as worlds of our model. *)

Variable AdAx : form -> Prop.


Class segment Γ : Type :=
  { head : @Ensemble form ;
    tail : @Ensemble (@Ensemble form) ;

    (* head and tail of the segment are included in (Clos Γ) *)
    segInclClos : forall th, (th = head \/ tail th) -> Included _ th (Clos Γ) ;
    (* head and tail of the segment are deductively closed with (Clos Γ) *)
    segClosed : forall th, (th = head \/ tail th) -> restr_closed AdAx (Clos Γ) th ;
    (* head and tail of the segment are quasi-prime *)
    segPrime : forall th, (th = head \/ tail th) -> quasi_prime th ;

    (* Boxed formulas in the head are reflected in the tail *)
    boxreflect : forall A, head (□ A) -> forall th, tail th -> th A ;
    (* Diamond formulas in the head are witnessed in the tail *)
    diamwitness : forall A, head (◊ A) -> exists th, tail th /\ th A
  }.

(* We admit that the proofs of the properties of segments are
    irrelevant to the identity between segments. *)

Axiom segment_prf_irrel : forall Γ (s0 s1 : segment Γ),
                (@head _ s0) = (@head _ s1) ->
                (@tail _ s0) = (@tail _ s1) ->
                s0 = s1.

(* Exploding world of the canonical model. *)

Lemma cexpl_segInclClos Γ : forall th, (th = (Clos Γ) \/ (Singleton _ (Clos Γ)) th) -> Included _ th (Clos Γ).
Proof.
intros. destruct H ; subst ; intros A HA ; auto. inversion H ; subst ; auto.
Qed.

Lemma cexpl_segClosed Γ : forall th, (th = (Clos Γ) \/ (Singleton _ (Clos Γ)) th) ->  restr_closed AdAx (Clos Γ) th.
Proof.
intros. destruct H ; subst ; intros A HA0 HA1 ; auto. inversion H ; subst ; auto.
Qed.

Lemma cexpl_segPrime Γ : forall th, (th = (Clos Γ) \/ (Singleton _ (Clos Γ)) th) -> quasi_prime th.
Proof.
intros. destruct H ; subst ; intros A B H0 H1. 
- apply H1. left. apply Incl_ClosSubform_Clos. unfold In. exists (A ∨ B) ; split ; auto.
  simpl ; right. apply in_or_app ; left. destruct A ; cbn ; auto.
- inversion H ; subst. apply H1. left. apply Incl_ClosSubform_Clos.
  unfold In. exists (A ∨ B) ; split ; auto. simpl ; right. apply in_or_app ; left.
  destruct A ; cbn ; auto.
Qed.

Lemma cexpl_boxreflect Γ : forall A, (Clos Γ) (□ A) -> forall th, (Singleton _ (Clos Γ)) th -> th A.
Proof.
intros. inversion H0 ; subst. apply Incl_ClosSubform_Clos. unfold In. exists (□ A) ; split ; auto.
  simpl ; right. destruct A ; cbn ; auto.
Qed.

Lemma cexpl_diamwitness Γ : forall A, (Clos Γ) (◊ A) -> exists th, (Singleton _ (Clos Γ)) th /\ th A.
Proof.
intros. exists (Clos Γ). split. apply In_singleton. 
apply Incl_ClosSubform_Clos. unfold In. exists (◊ A) ; split ; auto.
simpl ; right. destruct A ; cbn ; auto.
Qed.

Instance cexpl Γ : segment Γ :=
  {| head := Clos Γ ;
     tail := Singleton _ (Clos Γ) ;

     segInclClos := cexpl_segInclClos Γ ;
     segClosed := cexpl_segClosed Γ ;
     segPrime := cexpl_segPrime Γ ;
     boxreflect := cexpl_boxreflect Γ ;
     diamwitness := cexpl_diamwitness Γ
   |}.

(* Intuitionistic relation on the canonical model. *)

Definition cireach Γ (P0 P1 : segment Γ) : Prop :=
  Included _ (@head _ P0) (@head _ P1).

Lemma cireach_refl Γ u : cireach Γ u u.
Proof.
unfold cireach. intro. auto.
Qed.

Lemma cireach_trans Γ u v w: cireach Γ u v -> cireach Γ v w -> cireach Γ u w.
Proof.
intros. unfold cireach.
intro. intros. unfold cireach in H0. unfold cireach in H.
apply H0. apply H. auto.
Qed.

Lemma cireach_expl Γ u : cireach Γ (cexpl Γ) u -> u = (cexpl Γ).
Proof.
intros.
assert (@head _ u = @head _ (cexpl Γ)).
{ apply Extensionality_Ensembles. split ; intros C HC ; auto.
  unfold In in *. unfold head in *. apply segInclClos in HC ; auto. }
assert (@tail _ u = @tail _ (cexpl Γ)).
{ apply Extensionality_Ensembles. split ; intros C HC ; auto.
  - unfold In in *. unfold tail in *. unfold cexpl.
    assert (C = Clos Γ). apply Extensionality_Ensembles.
    split ; intros A HA ; auto. apply segInclClos in HA ; auto.
    assert (In form C Bot). apply boxreflect ; auto. rewrite H0.
    unfold head. unfold cexpl. unfold Clos. auto.
    apply segClosed ; auto. eapply MP. apply EFQ. apply Id ; auto.
    subst. apply In_singleton.
  - unfold In in *. unfold tail in *. unfold cexpl in HC. inversion HC ; subst.
    assert ((@head _ u) (◊ ⊥)). rewrite H0. unfold head. unfold cexpl. unfold Clos. auto.
    pose (diamwitness _ H1). destruct e. destruct H2.
    assert (x = Clos Γ). apply Extensionality_Ensembles.
    split ; intros A HA ; auto. apply segInclClos in HA ; auto.
    apply segClosed ; auto. eapply MP. apply EFQ. apply Id ; auto. subst. auto. }
apply segment_prf_irrel ; auto.
Qed.

(* Modal relation *)

Definition cmreach Γ (P0 P1 : segment Γ) : Prop :=
  (@tail _ P0) (@head _ P1).

Lemma cmreach_expl Γ u : cmreach Γ (cexpl Γ) u <-> u = (cexpl Γ).
Proof.
split ; intro ; subst.
- assert (@head _ u = @head _ (cexpl Γ)). inversion H ; auto.
  assert (@tail _ u = @tail _ (cexpl Γ)).
  { apply Extensionality_Ensembles. split ; intros C HC ; auto.
    * unfold In in *. unfold tail in *. unfold cexpl.
      assert (C = Clos Γ). apply Extensionality_Ensembles.
      split ; intros A HA ; auto. apply segInclClos in HA ; auto.
      assert (In form C Bot). apply boxreflect ; auto. rewrite H0.
      unfold head. unfold cexpl. unfold Clos. auto.
      apply segClosed ; auto. eapply MP. apply EFQ. apply Id ; auto.
      subst. apply In_singleton.
    * unfold In in *. unfold tail in *. unfold cexpl in HC. inversion HC ; subst.
      assert ((@head _ u) (◊ ⊥)). rewrite H0. unfold head. unfold cexpl. unfold Clos. auto.
      pose (diamwitness _ H1). destruct e. destruct H2.
      assert (x = Clos Γ). apply Extensionality_Ensembles.
      split ; intros A HA ; auto. apply segInclClos in HA ; auto.
      apply segClosed ; auto. eapply MP. apply EFQ. apply Id ; auto. subst. auto. }
  apply segment_prf_irrel ; auto.
- unfold cmreach. unfold tail. unfold head. unfold cexpl. apply In_singleton.
Qed.

(* We can define the canonical frame. *)

Instance CF Γ : frame :=
      {|
        nodes := segment Γ ;
        expl:= cexpl Γ ;

        ireachable := cireach Γ;
        ireach_refl := cireach_refl Γ ;
        ireach_tran := cireach_trans Γ ;
        ireach_expl := cireach_expl Γ ;

        mreachable := cmreach Γ ;
        mreach_expl := cmreach_expl Γ ;
      |}.

(* As expected, we can create canonical worlds using our
   Lindenbaum lemma. *)

Lemma Lindenbaum_segment Γ ψ Δ :
  In _ (Clos Γ) ψ ->
  Included _ Δ (Clos Γ) ->
  ~ extCKH_prv AdAx Δ ψ ->
  exists w : segment Γ, Included _ Δ head /\ ~ In _ head ψ.
Proof.
  intros. pose (Lindenbaum _ _ _ _ H H0 H1).
  destruct s as (Δm & H2 & H3 & H4 & H5 & H6).
  pose (Build_segment Γ Δm (Singleton _ (Clos Γ))); intros.
  eexists (s _ _ _ _ _) ; split ; auto. intro. apply H6. apply Id ; auto.
  Unshelve. all: intros ; auto.
  - destruct H7 ; subst ; auto. apply segInclClos ; auto.
  - destruct H7 ; subst ; auto. apply segClosed ; auto.
  - destruct H7 ; subst ; auto. eapply segPrime ; auto. inversion H7 ; subst.
    right. unfold tail. unfold cexpl. apply In_singleton.
  - inversion H8 ; subst. apply H3 in H7. apply Incl_ClosSubform_Clos.
    exists (□ A). split ; auto. cbn. right. destruct A ; cbn ; auto.
  - exists (Clos Γ). split ; auto. apply In_singleton. apply Incl_ClosSubform_Clos.
    exists (◊ A). split ; auto. cbn. right. destruct A ; cbn ; auto.
Qed.

(* We can show an existence lemma for diamond. *)

Lemma Diam_existence Γ (s : segment Γ) ψ :
  In _ (Clos Γ) (◊ ψ) ->
  ~ (@head _ s) (◊ ψ) ->
  exists w : segment Γ, Included _ (@head _ s) (@head _ w) /\
                                    forall th, (@tail _ w) th -> ~ th ψ.
Proof.
intros.
assert (Jψ: Clos Γ ψ).
{ apply Incl_ClosSubform_Clos. unfold In. exists (◊ ψ). split ; simpl ; auto. right.
  destruct ψ ; simpl ; auto. }
assert (R0: forall B, (@head _ s) (◊ B) -> ~ extCKH_prv AdAx (fun x => exists A, B = x \/ ((@head _ s) (□ A) /\ x = A)) ψ).
{ intros B HB D. apply H0. apply segClosed ; auto.
  apply extCKH_monot with (Γ1:= Union _ (fun x : form => exists A : form, (@head _ s) (□ A) /\ x = A) (Singleton _ B)) in D.
  apply extCKH_Deduction_Theorem in D. eapply MP. eapply MP. apply Ax ; left ; right ; eapply Kd ; reflexivity.
  apply K_rule in D. apply (extCKH_monot _ _ _ D). intros C HC. unfold In in *.
  destruct HC as (E & (F & HF0 & HF1) & HCE) ; subst ; auto. apply Id ; auto.
  intros C HC. unfold In in *. destruct HC as (E & [HE | (HE0 & HE1)]) ; subst ; auto.
  right ; apply In_singleton. left. exists E ; auto. }
assert (R2: forall B, (@head _ s) (◊ B) -> Included form (fun x => exists A, B = x \/ ((@head _ s) (□ A) /\ x = A)) (Clos Γ)).
{ intros B HB C HC. destruct HC as (D & [HD | (HD0 & HD1)]) ; subst ; auto.
  apply Incl_ClosSubform_Clos. exists (◊ C).
  split ; cbn ; auto. apply segInclClos in HB ; auto. right ; destruct C ; cbn ; auto.
  apply Incl_ClosSubform_Clos. exists (□ D).
  split ; cbn ; auto. apply segInclClos in HD0 ; auto. right ; destruct D ; cbn ; auto. }
remember (fun x => exists B (P: (@head _ s) (◊ B)), x = proj1_sig (Lindenbaum _ _ _ ψ Jψ (R2 _ P) (R0 _ P))) as LindSet.
assert (forall th : Ensemble form, th = head \/ LindSet th -> Included form th (Clos Γ)).
intros. destruct H1 ; subst ; auto. pose (@segInclClos _ s). apply i ; auto.
destruct H1 as (B & HB & J) ; subst. intros C HC. unfold In in *.
destruct (Lindenbaum _ Γ (fun x : form => exists A : form, B = x \/ head (□ A) /\ x = A) ψ Jψ 
(R2 B HB) (R0 B HB)) as (Γ0 & L0 & L1 & L2 & L3 & L4) ; cbn in *. apply L1 in HC ; auto.
assert (forall th : Ensemble form, th = head \/ LindSet th -> restr_closed AdAx (Clos Γ) th).
intros. destruct H2 ; subst ; auto. apply (@segClosed _ s) ; auto.
destruct H2 as (B & HB & J) ; subst. intros C HC0 HC1.
destruct (Lindenbaum _ Γ (fun x : form => exists A : form, B = x \/ head (□ A) /\ x = A) ψ Jψ 
(R2 B HB) (R0 B HB)) as (Γ0 & L0 & L1 & L2 & L3 & L4) ; cbn in *. apply L2 in HC1 ; auto.
assert (forall th : Ensemble form, th = head \/ LindSet th -> quasi_prime th).
intros. destruct H3 ; subst ; auto. eapply (@segPrime _ s) ; auto. 
destruct H3 as (B & HB & J) ; subst. intros C D Hor G.
destruct (Lindenbaum _ Γ (fun x : form => exists A : form, B = x \/ head (□ A) /\ x = A) ψ Jψ 
(R2 B HB) (R0 B HB)) as (Γ0 & L0 & L1 & L2 & L3 & L4) ; cbn in *. apply L3 in Hor ; auto.
assert (forall A : form, head (□ A) -> forall th : Ensemble form, LindSet th -> th A).
intros. rewrite HeqLindSet in H5. destruct H5 as (B & HB & J) ; subst.
destruct (Lindenbaum _ Γ (fun x : form => exists A : form, B = x \/ head (□ A) /\ x = A) ψ Jψ 
(R2 B HB) (R0 B HB)) as (Γ0 & L0 & L1 & L2 & L3 & L4) ; cbn in *.
apply L0. unfold In. exists A ; auto.
assert (forall A : form, head (◊ A) -> exists th : Ensemble form, LindSet th /\ th A).
intros.
destruct (Lindenbaum _ Γ (fun x : form => exists B : form, A = x \/ head (□ B) /\ x = B) ψ Jψ
(R2 _ H5) (R0 _ H5)) as (Γ0 & L0 & L1 & L2 & L3 & L4) eqn:E; cbn in *.
exists Γ0. split ; auto. rewrite HeqLindSet. exists A. exists H5 ; auto. rewrite E.
auto. apply L0. exists A ; auto.
pose (Build_segment Γ head LindSet H1 H2 H3 H4 H5).
exists s0. split ; auto. intros C HC ; auto.
intros th Hth contr. unfold tail in Hth. cbn in Hth. rewrite HeqLindSet in Hth.
destruct Hth as (B & HB & J) ; subst.
destruct (Lindenbaum _ Γ (fun x : form => exists A : form, B = x \/ head (□ A) /\ x = A) ψ Jψ
(R2 B HB) (R0 B HB)) as (Γ0 & L0 & L1 & L2 & L3 & L4) ; cbn in * ; subst.
apply L4. apply Id. auto.
Qed.

(* We define the canonical valuation. *)

Definition cval Γ s (p : nat) := ((@head Γ s) (# p) /\ (Clos Γ) (# p)) \/ ~ (Clos Γ) (# p).

Lemma cval_persist : forall Γ u v, cireach Γ u v -> forall (p : nat), cval Γ u p -> cval Γ v p.
Proof.
intros. unfold cval in *. destruct H0 ; auto. destruct H0. left. 
split ; auto. unfold head in *. apply H. auto.
Qed.

Lemma cval_expl Γ : forall p, (cval Γ) (cexpl Γ) p.
Proof.
intros. unfold cval. destruct (LEM (Clos Γ # p)) ; auto.
Qed.



(* Finally we can define the canonical model. *)

Instance CM Γ : model :=
      {|
        fra := CF Γ ;

        val := cval Γ ;
        persist :=  cval_persist Γ ;
        val_expl :=  cval_expl Γ
      |}.

(* Then we can prove the truth lemma. *)

Lemma truth_lemma Γ : forall ψ (s : segment Γ),
  (Clos Γ ψ) ->
  (forces (CM Γ) s ψ <-> (@head _ s) ψ).
Proof.
induction ψ ; intros ; split ; intros ; simpl ; try simpl in H1 ; auto.
(* nat *)
- inversion H0 ; try contradiction. firstorder.
- unfold cval. left ; auto.
(* Bot *)
- inversion H0 ; subst. unfold head. unfold expl ; cbn ; auto.
- assert (@head _ s = @head _ (cexpl Γ)). unfold head. unfold cexpl.
  { apply Extensionality_Ensembles. split ; intros C HC ; auto.
    * unfold In in *. apply segInclClos in HC ; auto.
    * unfold In in *. apply segClosed ; auto. eapply MP.
      apply EFQ. apply Id ; auto. }
  assert (@tail _ s = @tail _ (cexpl Γ)).
  { apply Extensionality_Ensembles. split ; intros C HC ; auto.
    * unfold In in *. unfold tail in *. unfold cexpl.
      assert (C = Clos Γ). apply Extensionality_Ensembles.
      split ; intros A HA ; auto. apply segInclClos in HA ; auto.
      assert (In form C Bot). apply boxreflect ; auto. rewrite H1.
      unfold head. unfold cexpl. unfold Clos. auto.
      apply segClosed ; auto. eapply MP. apply EFQ. apply Id ; auto.
      subst. apply In_singleton.
    * unfold In in *. unfold tail in *. unfold cexpl in HC. inversion HC ; subst.
      assert ((@head _ s) (◊ ⊥)). rewrite H1. unfold head. unfold cexpl. unfold Clos. auto.
      pose (diamwitness _ H2). destruct e. destruct H3.
      assert (x = Clos Γ). apply Extensionality_Ensembles.
      split ; intros A HA ; auto. apply segInclClos in HA ; auto.
      apply segClosed ; auto. eapply MP. apply EFQ. apply Id ; auto. subst. auto. }
  apply segment_prf_irrel ; auto.
(* And ψ1 ψ2 *)
- assert (Jψ1: Clos Γ ψ1).
  apply Incl_ClosSubform_Clos. unfold In. exists (ψ1 ∧ ψ2). split ; simpl ; auto. right.
  apply in_or_app ; left ; destruct ψ1 ; simpl ; auto.
  assert (Jψ2: Clos Γ ψ2).
  apply Incl_ClosSubform_Clos. unfold In. exists (ψ1 ∧ ψ2). split ; simpl ; auto. right.
  apply in_or_app ; right ; destruct ψ2 ; simpl ; auto.
  destruct H0. apply IHψ1 in H0 ; auto. apply IHψ2 in H1 ; auto. apply segClosed ; auto.
  eapply MP. eapply MP. eapply MP. apply Ax ; left ; left ; eapply IA8 ; reflexivity.
  apply imp_Id_gen. eapply MP. apply Thm_irrel. 1-2: apply Id ; auto.
- assert (Jψ1: Clos Γ ψ1).
  apply Incl_ClosSubform_Clos. unfold In. exists (ψ1 ∧ ψ2). split ; simpl ; auto. right.
  apply in_or_app ; left ; destruct ψ1 ; simpl ; auto.
  assert (Jψ2: Clos Γ ψ2).
  apply Incl_ClosSubform_Clos. unfold In. exists (ψ1 ∧ ψ2). split ; simpl ; auto. right.
  apply in_or_app ; right ; destruct ψ2 ; simpl ; auto.
  split.
  apply IHψ1 ; auto. apply segClosed ; auto. eapply MP.
  apply Ax ; left ; left ; eapply IA6 ; reflexivity. apply Id. exact H0.
  apply IHψ2 ; auto. apply segClosed ; auto. eapply MP.
  apply Ax ; left ; left ; eapply IA7 ; reflexivity. apply Id. exact H0.
(* Or ψ1 ψ2 *)
- assert (Jψ1: Clos Γ ψ1).
  apply Incl_ClosSubform_Clos. unfold In. exists (ψ1 ∨ ψ2). split ; simpl ; auto. right.
  apply in_or_app ; left ; destruct ψ1 ; simpl ; auto.
  assert (Jψ2: Clos Γ ψ2).
  apply Incl_ClosSubform_Clos. unfold In. exists (ψ1 ∨ ψ2). split ; simpl ; auto. right.
  apply in_or_app ; right ; destruct ψ2 ; simpl ; auto.
  destruct H0.
  apply IHψ1 in H0 ; auto. apply segClosed ; auto. eapply MP.
  apply Ax ; left ; left ; eapply IA3 ; reflexivity. apply Id. exact H0.
  apply IHψ2 in H0 ; auto. apply segClosed ; auto. eapply MP.
  apply Ax ; left ; left ; eapply IA4 ; reflexivity. apply Id. exact H0.
- assert (Jψ1: Clos Γ ψ1).
  apply Incl_ClosSubform_Clos. unfold In. exists (ψ1 ∨ ψ2). split ; simpl ; auto. right.
  apply in_or_app ; left ; destruct ψ1 ; simpl ; auto.
  assert (Jψ2: Clos Γ ψ2).
  apply Incl_ClosSubform_Clos. unfold In. exists (ψ1 ∨ ψ2). split ; simpl ; auto. right.
  apply in_or_app ; right ; destruct ψ2 ; simpl ; auto.
  assert (quasi_prime head). apply segPrime ; auto.
  apply LEM_prime in H1. destruct (H1 ψ1 ψ2) ; auto.
  left. apply IHψ1 ; auto.
  right. apply IHψ2 ; auto.
(* Imp ψ1 ψ2 *)
- assert (Jψ1: Clos Γ ψ1).
  apply Incl_ClosSubform_Clos. unfold In. exists (ψ1 → ψ2). split ; simpl ; auto. right.
  apply in_or_app ; left ; destruct ψ1 ; simpl ; auto.
  assert (Jψ2: Clos Γ ψ2).
  apply Incl_ClosSubform_Clos. unfold In. exists (ψ1 → ψ2). split ; simpl ; auto. right.
  apply in_or_app ; right ; destruct ψ2 ; simpl ; auto.
  destruct (LEM (head (ψ1 → ψ2))) ; auto. exfalso.
  assert (~ extCKH_prv AdAx (Union _ head (Singleton _ ψ1)) ψ2).
  intro. apply extCKH_Deduction_Theorem in H2. apply H1. apply segClosed ; auto.
  assert (Included form (Union _ head (Singleton form ψ1)) (Clos Γ)).
  intros A HA. inversion HA ; subst ; unfold In ; unfold Clos.
  apply segInclClos in H3 ; auto. inversion H3 ; subst ;  auto.
  pose (Lindenbaum_segment _ _ _ Jψ2 H3 H2). destruct e as [w [Hw1 Hw2]].
  assert (J2: cireach _ s w). unfold cireach.
  intros A HA. apply Hw1. apply Union_introl. auto. simpl in H0.
  pose (H0 _ J2). apply Hw2. apply IHψ2 ; auto. apply f. apply IHψ1 ; auto.
  apply segClosed ; auto. apply Id. apply Hw1.
  apply Union_intror ; apply In_singleton.
- assert (Jψ1: Clos Γ ψ1).
  apply Incl_ClosSubform_Clos. unfold In. exists (ψ1 → ψ2). split ; simpl ; auto. right.
  apply in_or_app ; left ; destruct ψ1 ; simpl ; auto.
  assert (Jψ2: Clos Γ ψ2).
  apply Incl_ClosSubform_Clos. unfold In. exists (ψ1 → ψ2). split ; simpl ; auto. right.
  apply in_or_app ; right ; destruct ψ2 ; simpl ; auto.
  intros.
  apply IHψ1 in H2 ; auto. unfold cireach in H1. apply H1 in H0.
  apply IHψ2 ; auto.
  assert (extCKH_prv AdAx head ψ2). eapply MP. apply Id ; exact H0.
  apply Id ; auto. apply segClosed ; auto.
(* Box ψ *)
- assert (Jψ: Clos Γ ψ).
  apply Incl_ClosSubform_Clos. unfold In. exists (Box ψ). split ; simpl ; auto. right.
  destruct ψ ; simpl ; auto. simpl in H0.
  destruct (LEM (head (□ ψ))) ; auto. exfalso.
  assert (~ extCKH_prv AdAx (fun x => exists A, (@head _ s) (□ A) /\ x = A) ψ).
  intro. apply H1. apply segClosed ; auto. apply K_rule in H2.
  apply (extCKH_monot _ _ _ H2). intros B HB. unfold In in *.
  destruct HB as (C & (D & HD0 & HD1) & HC) ; subst ; auto.
  apply Lindenbaum with (Γ:=Γ) in H2 ; auto.
  destruct H2 as (Γ0 & J0 & J1 & J2 & J3 & J4).
  assert (forall th : Ensemble form, th = head \/ (fun x => x = Γ0 \/ x = (Clos Γ)) th -> Included form th (Clos Γ)).
  intros. destruct H2 ; subst ; auto. pose (@segInclClos _ s). apply i ; auto. inversion H2 ; subst. 1-2: intros C HC ; auto.
  assert (forall th : Ensemble form, th = head \/ (fun x => x = Γ0 \/ x = (Clos Γ)) th -> restr_closed AdAx (Clos Γ) th).
  intros. destruct H3 ; subst ; auto. apply (@segClosed _ s) ; auto. inversion H3 ; subst. 1-2: intros C HC J ; auto.
  assert (forall th : Ensemble form, th = head \/ (fun x => x = Γ0 \/ x = (Clos Γ)) th -> quasi_prime th).
  intros. destruct H4 ; subst ; auto. eapply (@segPrime _ s) ; auto. inversion H4 ; subst.
  1-2: intros A B K0 K1. apply J3 in K0 ; auto. apply K1. left. apply Incl_ClosSubform_Clos. exists (A ∨ B).
  split ; auto. cbn. right. apply in_or_app ; left ; destruct A ; cbn ; auto.
  assert (forall A : form, head (□ A) -> forall th : Ensemble form, (fun x => x = Γ0 \/ x = (Clos Γ)) th -> th A).
  intros. inversion H6 ; subst. apply J0. unfold In. exists A ; split ; auto.
  apply Incl_ClosSubform_Clos. exists (□ A). split ; cbn ; auto.
  apply segInclClos in H5 ; auto. right ; destruct A ; cbn ; auto.
  assert (forall A : form, head (◊ A) -> exists th : Ensemble form, (fun x => x = Γ0 \/ x = (Clos Γ)) th /\ th A).
  intros. exists (Clos Γ). split ; auto. apply Incl_ClosSubform_Clos.
  exists (◊ A). split ; cbn ; auto. apply segInclClos in H6 ; auto. right ; destruct A ; cbn ; auto.
  pose (Build_segment Γ head (fun x => x = Γ0 \/ x = (Clos Γ)) H2 H3 H4 H5 H6).
  assert (cireach Γ s s0). intros C HC ; auto.
  assert (K0: forall th : Ensemble form, th = Γ0 \/ Singleton (Ensemble form) (Clos Γ) th -> Included form th (Clos Γ)).
  intros. destruct H8 ; subst ; auto. inversion H8 ; subst. intros C HC ; auto.
  assert (K1: forall th : Ensemble form, th = Γ0 \/ Singleton (Ensemble form) (Clos Γ) th -> restr_closed AdAx (Clos Γ) th).
  intros. destruct H8 ; subst ; auto. inversion H8. intros C HC J ; auto.
  assert (K2: forall th : Ensemble form, th = Γ0 \/ Singleton (Ensemble form) (Clos Γ) th -> quasi_prime th).
  intros. destruct H8 ; subst ; auto. inversion H8 ; subst.
  intros A B L0 L1. apply L1. left. apply Incl_ClosSubform_Clos. exists (A ∨ B).
  split ; auto. cbn. right. apply in_or_app ; left ; destruct A ; cbn ; auto.
  assert (K3: forall A : form, Γ0 (□ A) -> forall th : Ensemble form, Singleton (Ensemble form) (Clos Γ) th -> th A).
  intros. inversion H9 ; subst. apply Incl_ClosSubform_Clos. exists (□ A).
  split ; cbn ; auto. right ; destruct A ; cbn ; auto.
  assert (K4: forall A : form, Γ0 (◊ A) -> exists th : Ensemble form, Singleton (Ensemble form) (Clos Γ) th /\ th A).
  intros. exists (Clos Γ). split ; auto. apply In_singleton. apply Incl_ClosSubform_Clos.
  exists (◊ A). split ; cbn ; auto. right ; destruct A ; cbn ; auto.
  pose (Build_segment Γ Γ0 (Singleton _ (Clos Γ)) K0 K1 K2 K3 K4).
  apply H0 with (u:=s1) in H7. apply IHψ in H7 ; auto. apply J4. apply Id. auto.
  left ; auto. intros C HC. destruct HC as (D & HD0 & HD1) ; subst.
  apply Incl_ClosSubform_Clos. exists (□ D).
  split ; cbn ; auto. apply segInclClos in HD0 ; auto. right ; destruct D ; cbn ; auto.
- assert (Jψ: Clos Γ ψ).
  apply Incl_ClosSubform_Clos. unfold In. exists (Box ψ). split ; simpl ; auto. right.
  destruct ψ ; simpl ; auto.
  intros. apply IHψ ; auto. apply H1 in H0. pose (boxreflect _ H0). apply p ; auto.
(* Diam ψ *)
- assert (Jψ: Clos Γ ψ).
  apply Incl_ClosSubform_Clos. unfold In. exists (◊ ψ). split ; simpl ; auto. right.
  destruct ψ ; simpl ; auto.
  simpl in H0.
  destruct (LEM (head (◊ ψ))) ; auto. exfalso.
  destruct (Diam_existence _ _ _ H H1) as (s0 & J0 & J1).
  apply H0 in J0. destruct J0 as (u & Hu1 & Hu2).
  apply IHψ in Hu2 ; auto. apply J1 with (@head _ u) ; auto.
- assert (Jψ: Clos Γ ψ).
  apply Incl_ClosSubform_Clos. unfold In. exists (◊ ψ). split ; simpl ; auto. right.
  destruct ψ ; simpl ; auto.
  intros. unfold cireach in H1. apply H1 in H0.
  apply diamwitness in H0. destruct H0. destruct H0.
  assert (forall th : Ensemble form, th = x \/ Singleton (Ensemble form) (Clos Γ) th -> Included form th (Clos Γ)).
  intros. destruct H3 ; subst ; auto. pose (@segInclClos _ v). apply i ; auto. inversion H3 ; subst. intros C HC ; auto.
  assert (forall th : Ensemble form, th = x \/ Singleton (Ensemble form) (Clos Γ) th -> restr_closed AdAx (Clos Γ) th).
  intros. destruct H4 ; subst ; auto. apply (@segClosed _ v) ; auto. inversion H4. intros C HC J ; auto.
  assert (forall th : Ensemble form, th = x \/ Singleton (Ensemble form) (Clos Γ) th -> quasi_prime th).
  intros. destruct H5 ; subst ; auto. eapply (@segPrime _ v) ; auto. inversion H5 ; subst.
  intros A B J0 J1. apply J1. left. apply Incl_ClosSubform_Clos. exists (A ∨ B).
  split ; auto. cbn. right. apply in_or_app ; left ; destruct A ; cbn ; auto.
  assert (forall A : form, x (□ A) -> forall th : Ensemble form, Singleton (Ensemble form) (Clos Γ) th -> th A).
  intros. inversion H7 ; subst. apply Incl_ClosSubform_Clos. exists (□ A).
  split ; cbn ; auto. apply segInclClos in H6 ; auto. right ; destruct A ; cbn ; auto.
  assert (forall A : form, x (◊ A) -> exists th : Ensemble form, Singleton (Ensemble form) (Clos Γ) th /\ th A).
  intros. exists (Clos Γ). split ; auto. apply In_singleton. apply Incl_ClosSubform_Clos.
  exists (◊ A). split ; cbn ; auto. apply segInclClos in H7 ; auto. right ; destruct A ; cbn ; auto.
  pose (Build_segment Γ x (Singleton _ (Clos Γ)) H3 H4 H5 H6 H7).
  exists s0. split ; auto. apply IHψ ; auto.
Qed.

(* We leverage the truth lemma to prove a general completeness result parametrised
    in a set of additional axioms validated by a certain class of frames. Completeness
    on this class of frame follows. *)

Variable ClassF : frame -> Prop.
Hypothesis ClassF_AdAx : forall f, ClassF f -> (forall A, AdAx A -> fvalid f A).
Hypothesis CF_ClassF : forall Γ, ClassF (CF Γ).

Theorem QuasiCompleteness : forall Γ φ,
    ~ extCKH_prv AdAx Γ φ -> ~ loc_conseq ClassF Γ φ.
Proof.
intros Γ φ D H.
apply Lindenbaum_segment with (Γ:=Union _ Γ (Singleton _ φ)) in D ; auto.
- destruct D as (w & H1 & H2).
  assert ((forall A, Γ A -> forces (CM _) w A)). intros. apply truth_lemma. 2: apply H1 ; auto.
  unfold Clos. left. apply Incl_Set_ClosSubform. left ; auto.
  apply H2. apply truth_lemma ; auto. unfold Clos. left. apply Incl_Set_ClosSubform.
  right ; apply In_singleton. apply H. apply CF_ClassF. auto.
- unfold Clos. left. apply Incl_Set_ClosSubform. right ; apply In_singleton.
- intros A HA. unfold Clos. unfold In in *. left. apply Incl_Set_ClosSubform. left ; auto.
Qed.

Theorem Strong_Completeness : forall Γ φ,
    loc_conseq ClassF Γ φ -> extCKH_prv AdAx Γ φ.
Proof.
intros Γ φ LC. pose (QuasiCompleteness Γ φ).
destruct (LEM (extCKH_prv AdAx Γ φ)) ; auto. exfalso.
apply n ; assumption.
Qed.

End general_seg_completeness.


  
