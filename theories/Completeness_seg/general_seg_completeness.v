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


Class segment : Type :=
  { head : @Ensemble form ;
    tail : @Ensemble (@Ensemble form) ;

    (* head and tail of the segment are deductively closed with (AllForm) *)
    segClosed : forall th, (th = head \/ tail th) -> closed AdAx th ;
    (* head and tail of the segment are quasi-prime *)
    segPrime : forall th, (th = head \/ tail th) -> quasi_prime th ;

    (* Boxed formulas in the head are reflected in the tail *)
    boxreflect : forall A, head (□ A) -> forall th, tail th -> th A ;
    (* Diamond formulas in the head are witnessed in the tail *)
    diamwitness : forall A, head (◊ A) -> exists th, tail th /\ th A
  }.

(* We admit that the proofs of the properties of segments are
    irrelevant to the identity between segments. *)

Axiom segment_prf_irrel : forall (s0 s1 : segment),
                (@head s0) = (@head s1) ->
                (@tail s0) = (@tail s1) ->
                s0 = s1.

(* Exploding world of the canonical model. *)

Lemma cexpl_segClosed : forall th, (th = AllForm \/ (Singleton _ AllForm) th) ->  closed AdAx th.
Proof.
intros. destruct H ; subst ; intros A HA. unfold AllForm ; auto.
inversion H ; subst ; unfold AllForm ; auto.
Qed.

Lemma cexpl_segPrime : forall th, (th = AllForm \/ (Singleton _ AllForm) th) -> quasi_prime th.
Proof.
intros. destruct H ; subst ; intros A B H0 H1. 
- apply H1. left. unfold AllForm ; auto.
- inversion H ; subst. apply H1. left. unfold AllForm ; auto.
Qed.

Lemma cexpl_boxreflect : forall A, AllForm (□ A) -> forall th, (Singleton _ AllForm) th -> th A.
Proof.
intros. inversion H0 ; subst. unfold AllForm ; auto.
Qed.

Lemma cexpl_diamwitness : forall A, AllForm (◊ A) -> exists th, (Singleton _ AllForm) th /\ th A.
Proof.
intros. exists AllForm. split. apply In_singleton.
unfold AllForm ; auto. 
Qed.

Instance cexpl : segment :=
  {| head := AllForm ;
     tail := Singleton _ AllForm ;

     segClosed := cexpl_segClosed ;
     segPrime := cexpl_segPrime ;
     boxreflect := cexpl_boxreflect ;
     diamwitness := cexpl_diamwitness
   |}.

(* Intuitionistic relation on the canonical model. *)

Definition cireach (P0 P1 : segment) : Prop :=
  Included _ (@head P0) (@head P1).

Lemma cireach_refl u : cireach u u.
Proof.
unfold cireach. intro. auto.
Qed.

Lemma cireach_trans u v w: cireach u v -> cireach v w -> cireach u w.
Proof.
intros. unfold cireach.
intro. intros. unfold cireach in H0. unfold cireach in H.
apply H0. apply H. auto.
Qed.

Lemma cireach_expl u : cireach cexpl u -> u = cexpl.
Proof.
intros.
assert (@head u = @head cexpl).
{ apply Extensionality_Ensembles. split ; intros C HC ; auto.
  unfold In in *. unfold head in *. cbn. unfold AllForm ; auto. }
assert (@tail u = @tail cexpl).
{ apply Extensionality_Ensembles. split ; intros C HC ; auto.
  - unfold In in *. unfold tail in *. unfold cexpl.
    assert (C = AllForm). apply Extensionality_Ensembles.
    split ; intros A HA ; auto. unfold In ; unfold AllForm ; auto.
    assert (In form C Bot). apply boxreflect ; auto. rewrite H0.
    unfold head. unfold cexpl. unfold AllForm ; auto.
    apply segClosed ; auto. eapply MP. apply EFQ. apply Id ; auto.
    subst. apply In_singleton.
  - unfold In in *. unfold tail in *. unfold cexpl in HC. inversion HC ; subst.
    assert ((@head u) (◊ ⊥)). rewrite H0. unfold head. unfold cexpl. unfold AllForm ; auto.
    pose (diamwitness _ H1). destruct e. destruct H2.
    assert (x = AllForm). apply Extensionality_Ensembles.
    split ; intros A HA ; auto. unfold In ; unfold AllForm ; auto.
    apply segClosed ; auto. eapply MP. apply EFQ. apply Id ; auto. subst. auto. }
apply segment_prf_irrel ; auto.
Qed.

(* Modal relation *)

Definition cmreach (P0 P1 : segment) : Prop :=
  (@tail P0) (@head P1).

Lemma cmreach_expl u : cmreach cexpl u <-> u = cexpl.
Proof.
split ; intro ; subst.
- assert (@head u = @head cexpl). inversion H ; auto.
  assert (@tail u = @tail cexpl).
  { apply Extensionality_Ensembles. split ; intros C HC ; auto.
    * unfold In in *. unfold tail in *. unfold cexpl.
      assert (C = AllForm). apply Extensionality_Ensembles.
      split ; intros A HA ; auto. unfold In ; unfold AllForm ; auto.
      assert (In form C Bot). apply boxreflect ; auto. rewrite H0.
      unfold head. unfold cexpl. unfold AllForm ; auto.
      apply segClosed ; auto. eapply MP. apply EFQ. apply Id ; auto.
      subst. apply In_singleton.
    * unfold In in *. unfold tail in *. unfold cexpl in HC. inversion HC ; subst.
      assert ((@head u) (◊ ⊥)). rewrite H0. unfold head. unfold cexpl. unfold AllForm ; auto.
      pose (diamwitness _ H1). destruct e. destruct H2.
      assert (x = AllForm). apply Extensionality_Ensembles.
      split ; intros A HA ; auto. unfold In ; unfold AllForm ; auto.
      apply segClosed ; auto. eapply MP. apply EFQ. apply Id ; auto. subst. auto. }
  apply segment_prf_irrel ; auto.
- unfold cmreach. unfold tail. unfold head. unfold cexpl. apply In_singleton.
Qed.

(* We can define the canonical frame. *)

Instance CF : frame :=
      {|
        nodes := segment ;
        expl:= cexpl ;

        ireachable := cireach;
        ireach_refl := cireach_refl ;
        ireach_tran := cireach_trans ;
        ireach_expl := cireach_expl ;

        mreachable := cmreach ;
        mreach_expl := cmreach_expl ;
      |}.

(* As expected, we can create canonical worlds using our
   Lindenbaum lemma. *)

Lemma Lindenbaum_segment ψ Δ :
  ~ extCKH_prv AdAx Δ ψ ->
  exists w : segment, Included _ Δ head /\ ~ In _ head ψ.
Proof.
  intros. pose (Lindenbaum _ _ _ H).
  destruct s as (Δm & H2 & H3 & H4).
  pose (Build_segment Δm (Singleton _ (AllForm))); intros.
  eexists (s _ _ _ _) ; split ; auto. intro. apply H4. apply Id ; auto.
  Unshelve. all: intros ; auto.
  - destruct H0 ; subst ; auto. apply segClosed ; auto.
  - destruct H4 ; destruct H0 ; subst ; auto. eapply segPrime ; auto.
  - inversion H1 ; subst. unfold AllForm ; auto.
  - exists (AllForm). split ; auto. apply In_singleton. unfold AllForm ; auto.
Qed.

(* We can show an existence lemma for diamond. *)

Lemma Diam_existence (s : segment) ψ :
  ~ (@head s) (◊ ψ) ->
  exists w : segment, Included _ (@head s) (@head w) /\
                                    forall th, (@tail w) th -> ~ th ψ.
Proof.
intros.
assert (R0: forall B, (@head s) (◊ B) -> ~ extCKH_prv AdAx (fun x => exists A, B = x \/ ((@head s) (□ A) /\ x = A)) ψ).
{ intros B HB D. apply H. apply segClosed ; auto.
  apply extCKH_monot with (Γ1:= Union _ (fun x : form => exists A : form, (@head s) (□ A) /\ x = A) (Singleton _ B)) in D.
  apply extCKH_Deduction_Theorem in D. eapply MP. eapply MP. apply Ax ; left ; right ; eapply Kd ; reflexivity.
  apply K_rule in D. apply (extCKH_monot _ _ _ D). intros C HC. unfold In in *.
  destruct HC as (E & (F & HF0 & HF1) & HCE) ; subst ; auto. apply Id ; auto.
  intros C HC. unfold In in *. destruct HC as (E & [HE | (HE0 & HE1)]) ; subst ; auto.
  right ; apply In_singleton. left. exists E ; auto. }
remember (fun x => exists B (P: (@head s) (◊ B)), x = proj1_sig (Lindenbaum _ _ ψ (R0 _ P))) as LindSet.
assert (forall th : Ensemble form, th = head \/ LindSet th -> closed AdAx th).
intros. destruct H0 ; subst ; auto. apply (@segClosed s) ; auto.
destruct H0 as (B & HB & J) ; subst. intros C HC0.
destruct (Lindenbaum _ (fun x : form => exists A : form, B = x \/ head (□ A) /\ x = A) ψ 
(R0 B HB)) as (Γ0 & L0 & L1 & L2) ; cbn in *. apply L1 in HC0 ; auto.
assert (forall th : Ensemble form, th = head \/ LindSet th -> quasi_prime th).
intros. destruct H1 ; subst ; auto. eapply (@segPrime s) ; auto. 
destruct H1 as (B & HB & J) ; subst. intros C D Hor G.
destruct (Lindenbaum _ (fun x : form => exists A : form, B = x \/ head (□ A) /\ x = A) ψ 
(R0 B HB)) as (Γ0 & L0 & L1 & L2) ; cbn in *. apply L2 in Hor ; auto.
assert (forall A : form, head (□ A) -> forall th : Ensemble form, LindSet th -> th A).
intros. rewrite HeqLindSet in H3. destruct H3 as (B & HB & J) ; subst.
destruct (Lindenbaum _ (fun x : form => exists A : form, B = x \/ head (□ A) /\ x = A) ψ 
(R0 B HB)) as (Γ0 & L0 & L1 & L2) ; cbn in *.
apply L0. unfold In. exists A ; auto.
assert (forall A : form, head (◊ A) -> exists th : Ensemble form, LindSet th /\ th A).
intros.
destruct (Lindenbaum _ (fun x : form => exists B : form, A = x \/ head (□ B) /\ x = B) ψ
(R0 _ H3)) as (Γ0 & L0 & L1 & L2) eqn:E; cbn in *.
exists Γ0. split ; auto. rewrite HeqLindSet. exists A. exists H3 ; auto. rewrite E.
auto. apply L0. exists A ; auto.
pose (Build_segment head LindSet H0 H1 H2 H3).
exists s0. split ; auto. intros C HC ; auto.
intros th Hth contr. unfold tail in Hth. cbn in Hth. rewrite HeqLindSet in Hth.
destruct Hth as (B & HB & J) ; subst.
destruct (Lindenbaum _ (fun x : form => exists A : form, B = x \/ head (□ A) /\ x = A) ψ
(R0 B HB)) as (Γ0 & L0 & L1 & L2) ; cbn in * ; subst.
apply L2. apply Id. auto.
Qed.

(* We define the canonical valuation. *)

Definition cval s (p : nat) := (@head s) (# p).

Lemma cval_persist : forall u v, cireach u v -> forall (p : nat), cval u p -> cval v p.
Proof.
intros. unfold cval in *. unfold head in *. apply H. auto.
Qed.

Lemma cval_expl : forall p, cval cexpl p.
Proof.
intros. unfold cval. unfold head ; cbn. unfold AllForm ; auto.
Qed.



(* Finally we can define the canonical model. *)

Instance CM : model :=
      {|
        fra := CF ;

        val := cval ;
        persist :=  cval_persist ;
        val_expl :=  cval_expl
      |}.

(* Then we can prove the truth lemma. *)

Lemma truth_lemma : forall ψ (s : segment),
  forces CM s ψ <-> (@head s) ψ.
Proof.
induction ψ ; intros ; split ; intros ; simpl ; try simpl in H1 ; auto.
(* Bot *)
- inversion H ; try contradiction. firstorder.
- assert (@head s = @head cexpl). unfold head. unfold cexpl.
  { apply Extensionality_Ensembles. split ; intros C HC ; auto.
    * unfold In in *. unfold AllForm ; auto.
    * unfold In in *. apply segClosed ; auto. eapply MP.
      apply EFQ. apply Id ; auto. }
  assert (@tail s = @tail cexpl).
  { apply Extensionality_Ensembles. split ; intros C HC ; auto.
    * unfold In in *. unfold tail in *. unfold cexpl.
      assert (C = AllForm). apply Extensionality_Ensembles.
      split ; intros A HA ; auto. unfold In ; unfold AllForm ; auto.
      assert (In form C Bot). apply boxreflect ; auto. rewrite H0.
      unfold head. unfold cexpl. unfold AllForm ; auto.
      apply segClosed ; auto. eapply MP. apply EFQ. apply Id ; auto.
      subst. unfold In. split. 
    * unfold In in *. unfold tail in *. unfold cexpl in HC. inversion HC ; subst.
      assert ((@head s) (◊ ⊥)). rewrite H0. unfold head. unfold cexpl. unfold AllForm ; auto.
      pose (diamwitness _ H1). destruct e. destruct H2.
      assert (x = AllForm). apply Extensionality_Ensembles.
      split ; intros A HA ; auto. unfold In ; unfold AllForm ; auto.
      apply segClosed ; auto. eapply MP. apply EFQ. apply Id ; auto. subst. auto. }
  apply segment_prf_irrel ; auto.
(* And ψ1 ψ2 *)
- destruct H. apply IHψ1 in H ; auto. apply IHψ2 in H0 ; auto. apply segClosed ; auto.
  eapply MP. eapply MP. eapply MP. apply Ax ; left ; left ; eapply IA8 ; reflexivity.
  apply imp_Id_gen. eapply MP. apply Thm_irrel. 1-2: apply Id ; auto.
- split.
  apply IHψ1 ; auto. apply segClosed ; auto. eapply MP.
  apply Ax ; left ; left ; eapply IA6 ; reflexivity. apply Id. exact H.
  apply IHψ2 ; auto. apply segClosed ; auto. eapply MP.
  apply Ax ; left ; left ; eapply IA7 ; reflexivity. apply Id. exact H.
(* Or ψ1 ψ2 *)
- destruct H.
  apply IHψ1 in H ; auto. apply segClosed ; auto. eapply MP.
  apply Ax ; left ; left ; eapply IA3 ; reflexivity. apply Id. exact H.
  apply IHψ2 in H ; auto. apply segClosed ; auto. eapply MP.
  apply Ax ; left ; left ; eapply IA4 ; reflexivity. apply Id. exact H.
- assert (quasi_prime head). apply segPrime ; auto.
  apply LEM_prime in H0. destruct (H0 ψ1 ψ2) ; auto.
  left. apply IHψ1 ; auto.
  right. apply IHψ2 ; auto.
(* Imp ψ1 ψ2 *)
- destruct (LEM (head (ψ1 → ψ2))) ; auto. exfalso.
  assert (~ extCKH_prv AdAx (Union _ head (Singleton _ ψ1)) ψ2).
  intro. apply extCKH_Deduction_Theorem in H1. apply H0. apply segClosed ; auto.
  pose (Lindenbaum_segment _ _ H1). destruct e as [w [Hw1 Hw2]].
  assert (J2: cireach s w). unfold cireach.
  intros A HA. apply Hw1. apply Union_introl. auto. simpl in H0.
  pose (H _ J2). apply Hw2. apply IHψ2 ; auto. apply f. apply IHψ1 ; auto.
  apply segClosed ; auto. apply Id. apply Hw1.
  apply Union_intror ; apply In_singleton.
- intros.
  apply IHψ1 in H1 ; auto. unfold cireach in H0. apply H0 in H.
  apply IHψ2 ; auto.
  assert (extCKH_prv AdAx head ψ2). eapply MP. apply Id ; exact H.
  apply Id ; auto. apply segClosed ; auto.
(* Box ψ *)
- destruct (LEM (head (□ ψ))) ; auto. exfalso.
  assert (~ extCKH_prv AdAx (fun x => exists A, (@head s) (□ A) /\ x = A) ψ).
  intro. apply H0. apply segClosed ; auto. apply K_rule in H1.
  apply (extCKH_monot _ _ _ H1). intros B HB. unfold In in *.
  destruct HB as (C & (D & HD0 & HD1) & HC) ; subst ; auto.
  apply Lindenbaum in H1 ; auto.
  destruct H1 as (Γ0 & J0 & J1 & J2 & J3).
  assert (forall th : Ensemble form, th = head \/ (fun x => x = Γ0 \/ x = (AllForm)) th -> closed AdAx th).
  intros. destruct H1 ; subst ; auto. apply (@segClosed s) ; auto. inversion H1 ; subst. 1-2: intros C HC ; auto.
  unfold AllForm ; auto.
  assert (forall th : Ensemble form, th = head \/ (fun x => x = Γ0 \/ x = (AllForm)) th -> quasi_prime th).
  intros. destruct H2 ; subst ; auto. eapply (@segPrime s) ; auto. inversion H2 ; subst.
  1-2: intros A B K0 K1. apply J2 in K0 ; auto. apply K1. left. unfold AllForm ; auto.
  assert (forall A : form, head (□ A) -> forall th : Ensemble form, (fun x => x = Γ0 \/ x = (AllForm)) th -> th A).
  intros. inversion H4 ; subst. apply J0. unfold In. exists A ; split ; auto. unfold AllForm ; auto.
  assert (forall A : form, head (◊ A) -> exists th : Ensemble form, (fun x => x = Γ0 \/ x = (AllForm)) th /\ th A).
  intros. exists (AllForm). split ; auto. unfold AllForm ; auto.
  pose (Build_segment head (fun x => x = Γ0 \/ x = (AllForm)) H1 H2 H3 H4).
  assert (cireach s s0). intros C HC ; auto.
  assert (K1: forall th : Ensemble form, th = Γ0 \/ Singleton (Ensemble form) (AllForm) th -> closed AdAx th).
  intros. destruct H6 ; subst ; auto. inversion H6. intros C HC ; unfold AllForm ; auto.
  assert (K2: forall th : Ensemble form, th = Γ0 \/ Singleton (Ensemble form) (AllForm) th -> quasi_prime th).
  intros. destruct H6 ; subst ; auto. inversion H6 ; subst.
  intros A B L0 L1. apply L1. left. unfold AllForm ; auto.
  assert (K3: forall A : form, Γ0 (□ A) -> forall th : Ensemble form, Singleton (Ensemble form) (AllForm) th -> th A).
  intros. inversion H7 ; subst. unfold AllForm ; auto.
  assert (K4: forall A : form, Γ0 (◊ A) -> exists th : Ensemble form, Singleton (Ensemble form) (AllForm) th /\ th A).
  intros. exists (AllForm). split ; auto. apply In_singleton. unfold AllForm ; auto.
  pose (Build_segment Γ0 (Singleton _ (AllForm)) K1 K2 K3 K4).
  apply H in H5.
  assert (@head s1 ψ).
  { apply IHψ. apply H5. unfold mreachable ; cbn. auto. }
  apply J3. apply Id. auto.
- intros. apply IHψ ; auto. apply H0 in H. pose (boxreflect _ H). apply p ; auto.
(* Diam ψ *)
- simpl in H.
  destruct (LEM (head (◊ ψ))) ; auto. exfalso.
  destruct (Diam_existence _ _ H0) as (s0 & J0 & J1).
  apply H in J0. destruct J0 as (u & Hu1 & Hu2).
  apply IHψ in Hu2 ; auto. apply J1 with (@head u) ; auto.
- intros. unfold cireach in H0. apply H0 in H.
  apply diamwitness in H. destruct H. destruct H.
  assert (forall th : Ensemble form, th = x \/ Singleton (Ensemble form) (AllForm) th -> closed AdAx th).
  intros. destruct H2 ; subst ; auto. apply (@segClosed v) ; auto. inversion H2. intros C HC ; unfold AllForm ; auto.
  assert (forall th : Ensemble form, th = x \/ Singleton (Ensemble form) (AllForm) th -> quasi_prime th).
  intros. destruct H3 ; subst ; auto. eapply (@segPrime v) ; auto. inversion H3 ; subst.
  intros A B J0 J1. apply J1. left. unfold AllForm ; auto.
  assert (forall A : form, x (□ A) -> forall th : Ensemble form, Singleton (Ensemble form) (AllForm) th -> th A).
  intros. inversion H5 ; subst. unfold AllForm ; auto.
  assert (forall A : form, x (◊ A) -> exists th : Ensemble form, Singleton (Ensemble form) (AllForm) th /\ th A).
  intros. exists (AllForm). split ; auto. apply In_singleton. unfold AllForm ; auto.
  pose (Build_segment x (Singleton _ (AllForm)) H2 H3 H4 H5).
  exists s0. split ; auto. apply IHψ ; auto.
Qed.

(* We leverage the truth lemma to prove a general completeness result parametrised
    in a set of additional axioms validated by a certain class of frames. Completeness
    on this class of frame follows. *)

Variable ClassF : frame -> Prop.
Hypothesis ClassF_AdAx : forall f, ClassF f -> (forall A, AdAx A -> fvalid f A).
Hypothesis CF_ClassF : ClassF CF.

Theorem QuasiCompleteness : forall Γ φ,
    ~ extCKH_prv AdAx Γ φ -> ~ loc_conseq ClassF Γ φ.
Proof.
intros Γ φ D H.
apply Lindenbaum_segment in D ; auto.
destruct D as (w & H1 & H2).
assert ((forall A, Γ A -> forces CM w A)). intros. apply truth_lemma. apply H1 ; auto.
apply H2. apply truth_lemma ; auto.
Qed.

Theorem Strong_Completeness : forall Γ φ,
    loc_conseq ClassF Γ φ -> extCKH_prv AdAx Γ φ.
Proof.
intros Γ φ LC. pose (QuasiCompleteness Γ φ).
destruct (LEM (extCKH_prv AdAx Γ φ)) ; auto. exfalso.
apply n ; assumption.
Qed.

End general_seg_completeness.


  
