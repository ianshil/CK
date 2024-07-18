Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.


Axiom LEM : forall P, P \/ ~ P.

Section general_segP_completeness.

Variable AdAx : form -> Prop.

Definition AdAxIdb := fun x => AdAx x \/ (exists A B, (Idb A B) = x).


(* We construct the P-segments for our canonical model *)

Class Psegment : Type :=
  { head : @Ensemble form ;
    tail : @Ensemble (@Ensemble form) ;

    (* head and tail are closed under deduction *)
    segClosed : forall th, (th = head \/ tail th) -> closed AdAxIdb th ;
    (* head and tail of the Psegment are quasi-prime *)
    segPrime : forall th, (th = head \/ tail th) -> prime th ;

    (* Psegment ⊥ *)
    segP_Bot : head ⊥ -> (forall th, tail th <-> th = AllForm) ;
    (* Psegment not ⊥ but  (⬦ ⊥) *)
    segP_noBot_DiamBot : ~ head ⊥ -> head (⬦ ⊥) -> (forall th, Theory AdAxIdb th -> (tail th <-> (fun x => forall C, head (Box C) -> x C) th)) ;
    (* Psegment not ⊥ not  (⬦ ⊥) *)
    segP_noBot_noDiamBot : ~ head ⊥ -> ~ head (⬦ ⊥) ->
                exists A, ~ head (⬦ A) /\ (forall th, Theory AdAxIdb th -> (tail th <-> (fun x => (forall C, head (Box C) -> x C) /\ ~ x A) th))
  }.

(* P-segments are also segments as the satisfy the two following properties. *)

Lemma boxreflect : forall seg A, (@head seg) (☐ A) -> forall th, (@tail seg) th -> th A.
Proof.
intros. destruct (LEM (head ⊥)).
- apply segP_Bot with th in H1. apply H1 in H0 ; subst.
  unfold AllForm ; auto.
- destruct (LEM (head (⬦ ⊥))).
  + apply segP_noBot_DiamBot with th in H1 ; auto. rewrite H1 in H0 ; subst.
     apply H0 ; auto. split ; [apply segClosed | apply segPrime] ; auto.
  + apply segP_noBot_noDiamBot in H2 ; auto. destruct H2 as (B & H3 & H4).
     apply H4 in H0. destruct H0. auto. split ; [apply segClosed | apply segPrime] ; auto.
Qed.

Lemma diamwitness : forall seg A, (@head seg) (⬦ A) -> exists th, (@tail seg) th /\ th A.
Proof.
intros. destruct (LEM (head ⊥)).
- pose (segP_Bot H0). exists AllForm. split ; auto. apply i ; auto.
  unfold AllForm ; auto.
- destruct (LEM (head (⬦ ⊥))).
  + pose (segP_noBot_DiamBot H0 H1). exists AllForm. split ; auto. apply i ; auto.
     apply Theory_AllForm. intros. all: unfold AllForm ; auto.
  + pose (segP_noBot_noDiamBot H0 H1). destruct e as (B & H2 & H3).
     assert (~ extCKH_prv AdAxIdb (Union _ (fun x => head (☐ x)) (Singleton _ A)) B).
     { intro. apply H2. apply segClosed ; auto. eapply MP. eapply MP.
       apply Ax ; left ; right ; eapply Kd ; reflexivity. apply extCKH_Deduction_Theorem in H4.
       apply K_rule in H4. apply (extCKH_monot _ _ _ H4).
       intros C HC ; inversion HC ; subst. destruct H5 ; subst. unfold In in H5 ; auto.
       apply Id ; auto. }
     apply Lindenbaum with (Γ:=AllForm) in H4 ; auto.
     destruct H4 as (Δ & K0 & K1 & K2 & K3 & K4). exists Δ. split ; auto.
     apply H3 ; auto. split. intros C HC ; apply K2 ; auto.
     left ; apply Incl_Set_ClosSubform ; unfold In ; unfold AllForm ; auto.
     apply LEM_prime ; auto.
     split ; intros ; auto. apply K0 ; left ; unfold In ; auto. intro. apply K4. apply Id ; auto.
     apply K0. right ; apply In_singleton.
     left ; apply Incl_Set_ClosSubform ; unfold In ; unfold AllForm ; auto.
     intros C HC ; left ; apply Incl_Set_ClosSubform ; unfold In ; unfold AllForm ; auto.
Qed.

(* We admit that the proofs of the properties of P-segments are
    irrelevant to the identity between Psegments. *)

Axiom Psegment_prf_irrel : forall (s0 s1 : Psegment),
                (@head s0) = (@head s1) ->
                (@tail s0) = (@tail s1) ->
                s0 = s1.

(* Exploding world of the canonical model. *)

Lemma cexpl_segClosed : forall th, (th = AllForm \/ (Singleton _ AllForm) th) ->  closed AdAxIdb th.
Proof.
intros. destruct H ; subst ; intros A HA ; auto. unfold AllForm ; auto.
inversion H ; subst ; auto. unfold AllForm ; auto.
Qed.

Lemma cexpl_segPrime : forall th, (th = AllForm \/ (Singleton _ AllForm) th) -> prime th.
Proof.
intros. destruct H ; subst ; intros A B H0 ; left ; unfold AllForm ; auto ; inversion H ; unfold AllForm ; auto.
Qed.

Lemma cexpl_segP_Bot : AllForm ⊥ -> (forall th, (Singleton _ AllForm) th <-> th = AllForm).
Proof.
intros. split ; intros.
- inversion H0 ; subst ; auto.
- subst ; apply In_singleton.
Qed.

Lemma cexpl_segP_noBot_DiamBot : ~ AllForm ⊥ -> AllForm (⬦ ⊥) -> (forall th, Theory AdAxIdb th -> ((Singleton _ AllForm) th <-> (fun x => forall C, AllForm (Box C) -> x C) th)).
Proof.
intros. exfalso. apply H. unfold AllForm ; auto.
Qed.

Lemma cexpl_segP_noBot_noDiamBot: ~ AllForm ⊥ -> ~ AllForm (⬦ ⊥) ->
    exists A, ~ AllForm (⬦ A) /\ (forall th, Theory AdAxIdb th -> ((Singleton _ AllForm) th <-> (fun x => (forall C, AllForm (Box C) -> x C) /\ ~ x A) th)).
Proof.
intros. exfalso. apply H. unfold AllForm ; auto.
Qed.

Instance cexpl : Psegment :=
  {| head := AllForm ;
    tail := Singleton _ AllForm ;

    segClosed := cexpl_segClosed ;
    segPrime := cexpl_segPrime ;

    segP_Bot := cexpl_segP_Bot ;
    segP_noBot_DiamBot := cexpl_segP_noBot_DiamBot ;
    segP_noBot_noDiamBot := cexpl_segP_noBot_noDiamBot
  |}.

(* Intuitionistic relation on the canonical model. *)

Definition cireach (s0 s1 : Psegment) : Prop :=
  Included _ (@head s0) (@head s1).

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
  unfold In in *. unfold head in *. unfold cexpl ; cbn ; unfold AllForm ; auto. }
assert (@tail  u = @tail  cexpl).
{ apply Extensionality_Ensembles. split ; intros C HC ; auto.
  - unfold In in *. unfold tail in *. unfold cexpl.
    assert (C = AllForm). apply Extensionality_Ensembles.
    split ; intros A HA ; auto. unfold AllForm ; unfold In ; auto.
    assert (In form C Bot). apply boxreflect with u ; auto. rewrite H0.
    unfold head. unfold cexpl. unfold AllForm. auto.
    apply segClosed ; auto. eapply MP. apply EFQ. apply Id ; auto.
    subst. apply In_singleton.
  - unfold In in *. unfold tail in *. unfold cexpl in HC. inversion HC ; subst.
    assert ((@head u) (⬦ ⊥)). rewrite H0. unfold head. unfold cexpl. unfold AllForm. auto.
    pose (diamwitness _ _ H1). destruct e. destruct H2.
    assert (x = AllForm). apply Extensionality_Ensembles.
    split ; intros A HA ; auto. unfold In ; unfold AllForm ; auto.
    apply segClosed ; auto. eapply MP. apply EFQ. apply Id ; auto. subst. auto. }
apply Psegment_prf_irrel ; auto.
Qed.

(* Modal relation *)

Definition cmreach (s0 s1 : Psegment) : Prop :=
  (@tail s0) (@head s1).

Lemma cmreach_expl u : cmreach cexpl u <-> u = cexpl.
Proof.
split ; intro ; subst.
- assert (@head u = @head cexpl). inversion H ; auto.
  assert (@tail  u = @tail  cexpl).
  { apply Extensionality_Ensembles. split ; intros C HC ; auto.
    * unfold In in *. unfold tail in *. unfold cexpl.
      assert (C = AllForm). apply Extensionality_Ensembles.
      split ; intros A HA ; auto. unfold In ; unfold AllForm ; auto.
      assert (In form C Bot). apply boxreflect with u ; auto. rewrite H0.
      unfold head. unfold cexpl. unfold Clos. auto.
      apply segClosed ; auto. eapply MP. apply EFQ. apply Id ; auto.
      subst. apply In_singleton.
    * unfold In in *. unfold tail in *. unfold cexpl in HC. inversion HC ; subst.
      assert ((@head u) (⬦ ⊥)). rewrite H0. unfold head. unfold cexpl. unfold AllForm. auto.
      pose (diamwitness _ _ H1). destruct e. destruct H2.
      assert (x = AllForm). apply Extensionality_Ensembles.
      split ; intros A HA ; auto. unfold In ; unfold AllForm ; auto.
      apply segClosed ; auto. eapply MP. apply EFQ. apply Id ; auto. subst. auto. }
  apply Psegment_prf_irrel ; auto.
- unfold cmreach. unfold tail. unfold head. unfold cexpl. apply In_singleton.
Qed.

(* We can define the canonical frame. *)

Instance CF : frame :=
      {|
        nodes := Psegment ;
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

Lemma Lindenbaum_Psegment ψ Δ :
  ~ extCKH_prv AdAxIdb Δ ψ ->
  exists w : Psegment, Included _ Δ head /\ ~ In _ head ψ.
Proof.
  intros H1.
  assert (J0: In form (Clos AllForm) ψ). left. apply Incl_Set_ClosSubform ; unfold In ; unfold AllForm ; auto.
  assert (J1: Included _ Δ (Clos AllForm)). intros C HC. left ; apply Incl_Set_ClosSubform ; unfold In ; unfold AllForm ; auto.
  pose (Lindenbaum _ _ _ _ J0 J1 H1).
  destruct s as (Δm & H2 & H3 & H4 & H5 & H6).
  destruct (LEM (Δm (⬦ ⊥))) as [P | NP].
  - pose (Build_Psegment Δm (fun th => Theory AdAxIdb th /\ (forall C, (Δm (☐ C) -> th C)))).
    eexists (p _ _ _ _ _) ; split ; auto. intro. apply H6. apply Id ; auto.
    Unshelve. all: intros ; auto.
    + destruct H ; subst ; auto. intros C HC ; apply H4 ; auto.
       left ; apply Incl_Set_ClosSubform ; unfold In ; unfold AllForm ; auto.
       destruct H. intros C HC ; apply H ; auto.
    + destruct H ; subst ; auto. apply LEM_prime ; auto. destruct H ; destruct H ; auto.
    + exfalso. apply H6. eapply MP. apply EFQ. apply Id ; auto.
    + split ; intros ; auto. destruct H8 as (H10 & H11). auto.
    + exists ⊥. split ; auto. intros. split ; intros. firstorder. firstorder.
  - pose (Build_Psegment Δm (fun th => Theory AdAxIdb th /\ (forall C, (Δm (☐ C) -> th C)) /\ ~ th ⊥)).
    eexists (p _ _ _ _ _) ; split ; auto. intro. apply H6. apply Id ; auto.
    Unshelve. all: intros ; auto.
    + destruct H ; subst ; auto. intros C HC ; apply H4 ; auto.
       left ; apply Incl_Set_ClosSubform ; unfold In ; unfold AllForm ; auto.
       destruct H. intros C HC ; apply H ; auto.
    + destruct H ; subst ; auto. apply LEM_prime ; auto. destruct H ; destruct H ; auto.
    + exfalso. apply H6. eapply MP. apply EFQ. apply Id ; auto.
    + split ; intros ; auto. destruct H8 as (H10 & H11 & H12). auto.
    + exists Bot. split ; auto. intros. split ; intros ; auto. split. firstorder.
       intro. firstorder.
Qed.

Lemma Lindenbaum_Psegment_Diam ψ Δ :
  Theory AdAxIdb Δ -> ~ Δ (⬦ ψ) ->
  exists w : Psegment, Δ = (@head w) /\ (forall th, Theory AdAxIdb th -> ((@tail w) th <-> (fun x => (forall C, (@head w) (Box C) -> x C) /\ ~ x ψ) th)).
Proof.
  intros H1 H2.
  assert (K0: forall th : Ensemble form, th = Δ \/ (fun x => Theory AdAxIdb x /\ (forall C, Δ (Box C) -> x C) /\ ~ x ψ) th -> closed AdAxIdb th).
  intros. destruct H ; subst ; auto. destruct H1 ; auto. destruct H ; destruct H ; auto.
  assert (K1: forall th : Ensemble form, th = Δ \/ (fun x => Theory AdAxIdb x /\ (forall C, Δ (Box C) -> x C) /\ ~ x ψ) th -> prime th).
  intros. destruct H ; subst ; auto. destruct H1 ; auto. destruct H ; destruct H ; auto.
  assert (K2: Δ ⊥ -> (forall th, (fun x => Theory AdAxIdb x /\ (forall C, Δ (Box C) -> x C) /\ ~ x ψ) th <-> th = AllForm)).
  intros. exfalso. apply H2. apply H1. eapply MP. apply EFQ. apply Id ; auto.
  assert (K3: ~ Δ ⊥ -> Δ (⬦ ⊥) -> (forall th, Theory AdAxIdb th -> ((fun x => Theory AdAxIdb x /\ (forall C, Δ (Box C) -> x C) /\ ~ x ψ) th <-> (fun x => forall C, Δ (Box C) -> x C) th))).
  intros. exfalso. apply H2. apply H1. eapply MP. eapply MP.
  apply Ax ; left ; right ; eapply Kd ; reflexivity. apply Nec. apply EFQ. apply Id ; auto.
  assert (K4: ~ Δ ⊥ -> ~ Δ (⬦ ⊥) ->
    exists A, ~ Δ (⬦ A) /\ (forall th, Theory AdAxIdb th -> ((fun x => Theory AdAxIdb x /\ (forall C, Δ (Box C) -> x C) /\ ~ x ψ) th <-> (fun x => (forall C, Δ (Box C) -> x C) /\ ~ x A) th))).
  intros. exists ψ. split ; auto. intros. split ; auto. intros. firstorder.
  pose (Build_Psegment _ _ K0 K1 K2 K3 K4).
  exists p ; split ; auto.
  split ; intros.
  - split ; intros.
    + apply boxreflect with (th:=th) in H3; auto.
    + intro. apply H0 in H3 ; auto.
  - destruct H0. split ; auto.
Qed.

(* We define the canonical valuation. *)

Definition cval s (p : nat) := (@head s) (# p).

Lemma cval_persist : forall u v, cireach u v -> forall (p : nat), cval u p -> cval v p.
Proof.
intros. unfold cval in *. apply H. auto.
Qed.

Lemma cval_expl : forall p, (cval) cexpl p.
Proof.
intros. unfold cval. unfold head ; unfold cexpl ; cbn ; unfold AllForm ; auto.
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

Lemma truth_lemma : forall ψ (s : Psegment),
  (forces CM s ψ <-> (@head s) ψ).
Proof.
induction ψ ; intros s ; split ; intros H0 ; simpl ; try simpl in H0 ; auto.
(* nat *)
- inversion H0. firstorder.
(* Bot *)
- assert (@head s = @head cexpl). unfold head. unfold cexpl.
  { apply Extensionality_Ensembles. split ; intros C HC ; auto.
    * unfold In in *. unfold AllForm ; auto.
    * unfold In in *. apply segClosed ; auto. eapply MP.
      apply EFQ. apply Id ; auto. }
  assert (@tail  s = @tail  cexpl).
  { apply Extensionality_Ensembles. split ; intros C HC ; auto.
    * unfold In in *. unfold tail in *. unfold cexpl.
      assert (C = AllForm). apply Extensionality_Ensembles.
      split ; intros A HA ; auto. unfold In ; unfold AllForm ; auto.
      assert (In form C Bot). apply boxreflect with s ; auto. rewrite H.
      unfold head. unfold cexpl. unfold Clos. auto.
      apply segClosed ; auto. eapply MP. apply EFQ. apply Id ; auto.
      subst. apply In_singleton.
    * unfold In in *. unfold tail in *. unfold cexpl in HC. inversion HC ; subst.
      assert ((@head s) (⬦ ⊥)). rewrite H. unfold head. unfold cexpl. unfold AllForm. auto.
      pose (diamwitness _ _ H1). destruct e. destruct H2.
      assert (x = AllForm). apply Extensionality_Ensembles.
      split ; intros A HA ; auto. unfold In ; unfold AllForm ; auto.
      apply segClosed ; auto. eapply MP. apply EFQ. apply Id ; auto. subst. auto. }
  apply Psegment_prf_irrel ; auto.
(* And ψ1 ψ2 *)
- destruct H0. apply IHψ1 in H ; auto. apply IHψ2 in H0 ; auto. apply segClosed ; auto.
  eapply MP. eapply MP. eapply MP. apply Ax ; left ; left ; eapply IA8 ; reflexivity.
  apply imp_Id_gen. eapply MP. apply Thm_irrel. 1-2: apply Id ; auto.
- split.
  apply IHψ1 ; auto. apply segClosed ; auto. eapply MP.
  apply Ax ; left ; left ; eapply IA6 ; reflexivity. apply Id. exact H0.
  apply IHψ2 ; auto. apply segClosed ; auto. eapply MP.
  apply Ax ; left ; left ; eapply IA7 ; reflexivity. apply Id. exact H0.
(* Or ψ1 ψ2 *)
- destruct H0.
  apply IHψ1 in H ; auto. apply segClosed ; auto. eapply MP.
  apply Ax ; left ; left ; eapply IA3 ; reflexivity. apply Id. exact H.
  apply IHψ2 in H ; auto. apply segClosed ; auto. eapply MP.
  apply Ax ; left ; left ; eapply IA4 ; reflexivity. apply Id. exact H.
- assert (prime head). apply segPrime ; auto.
  apply H in H0. destruct H0 ; auto.
  left. apply IHψ1 ; auto.
  right. apply IHψ2 ; auto.
(* Imp ψ1 ψ2 *)
- destruct (LEM (head (ψ1 --> ψ2))) ; auto. exfalso.
  assert (~ extCKH_prv AdAxIdb (Union _ head (Singleton _ ψ1)) ψ2).
  intro. apply extCKH_Deduction_Theorem in H1. apply H. apply segClosed ; auto.
  assert (Included form (Union _ head (Singleton form ψ1)) (Clos AllForm)).
  intros A HA. left. apply Incl_Set_ClosSubform ; unfold In ; unfold AllForm ; auto.
  pose (Lindenbaum_Psegment _ _ H1). destruct e as [w [Hw1 Hw2]].
  assert (J2: cireach s w). unfold cireach.
  intros A HA. apply Hw1. apply Union_introl. auto. simpl in H0.
  pose (H0 _ J2). apply Hw2. apply IHψ2 ; auto. apply f. apply IHψ1 ; auto.
  apply segClosed ; auto. apply Id. apply Hw1.
  apply Union_intror ; apply In_singleton.
- intros.
  apply IHψ1 in H1 ; auto. unfold cireach in H. apply H in H0.
  apply IHψ2 ; auto.
  assert (extCKH_prv AdAxIdb head ψ2). eapply MP. apply Id ; exact H0.
  apply Id ; auto. apply segClosed ; auto.
(* Box ψ *)
- destruct (LEM (head (☐ ψ))) ; auto. exfalso.
  assert (~ extCKH_prv AdAxIdb (fun x => exists A, (@head s) (☐ A) /\ x = A) ψ).
  intro. apply H. apply segClosed ; auto. apply K_rule in H1.
  apply (extCKH_monot _ _ _ H1). intros B HB. unfold In in *.
  destruct HB as (C & (D & HD0 & HD1) & HC) ; subst ; auto.
  apply Lindenbaum_Psegment  in H1 ; auto. destruct H1 as (s0 & H1 & H2).
  destruct (LEM ((@head s) (⬦ ⊥))) as [P | NP].
  { apply (@segP_noBot_DiamBot s) with (@head s0) in P ; auto.
    apply H2. apply IHψ. apply H0 with s. apply cireach_refl.
    apply P. intros. apply H1 ; unfold In ; exists C ; auto. intro H4. apply H.
    apply (@segClosed s) ; auto. eapply MP. apply EFQ. apply Id ; auto.
    split ; [apply segClosed | apply segPrime] ; auto. }
  { remember (fun x => Theory AdAxIdb x /\ (forall C, (@head s) (Box C) -> x C) /\ ~ x ⊥) as UBot.
    (* Need to create the UBot-tail of head. *)
    pose (Lindenbaum_Psegment_Diam ⊥ (@head s)). destruct e as (p & Hp0 & Hp1) ; subst ; auto.
    split ; [apply (@segClosed s) | apply (@segPrime s)] ; auto.
    assert (cireach s p). intros C HC ; rewrite <- Hp0 ; auto. apply H2. apply IHψ. apply H0 with p ; auto.
    unfold cmreach. apply Hp1. split ; [apply (@segClosed s0) | apply (@segPrime s0)] ; auto.
    split ; auto. intros. apply H1 ; exists C ; rewrite Hp0 ; auto. intro. apply H2. apply (@segClosed s0) ; auto.
    eapply MP. apply EFQ. apply Id ; auto. }
- intros. apply IHψ ; auto. apply H in H0. pose (boxreflect _ _ H0). apply p ; auto.
(* Diam ψ *)
- destruct (LEM (head (⬦ ψ))) ; auto. exfalso.
  remember (fun x => Theory AdAxIdb x /\ (forall C, (@head s) (Box C) -> x C) /\ ~ x ψ) as Upsi.
  (* Need to create the Upsi-tail of head. *)
  pose (Lindenbaum_Psegment_Diam ψ (@head s)). destruct e as (p & Hp0 & Hp1) ; subst ; auto.
  split ; [apply (@segClosed s) | apply (@segPrime s)] ; auto.
  assert (cireach s p). intros C HC ; rewrite <- Hp0 ; auto.
  apply H0 in H1. destruct H1 as (s0 & H6 & H7). apply IHψ in H7.
  pose (Hp1 (@head s0)). apply i ; auto. split ; [apply (@segClosed s0) | apply (@segPrime s0)] ; auto.
- intros. unfold cireach in H. apply H in H0.
  apply diamwitness in H0. destruct H0. destruct H0.
  (* We proceed to construct a segment for x. *)
  destruct (LEM (x ⊥ )) as [P | NP].
  { assert (forall th : Ensemble form, th = x \/ (Singleton _ AllForm) th -> closed AdAxIdb th).
    intros. destruct H2 ; subst ; auto. apply (@segClosed v) ; auto. inversion H2 ; subst. apply Theory_AllForm.
    assert (forall th : Ensemble form, th = x \/ (Singleton _ AllForm) th -> prime th).
    intros. destruct H3 ; subst ; auto. eapply (@segPrime v) ; auto. inversion H3 ; subst ; apply (@Theory_AllForm AdAxIdb).
    assert (x ⊥ -> (forall th, (Singleton _ AllForm) th <-> th = AllForm)).
    intros. split ; intros ; subst ; auto. inversion H5 ; subst ; auto. apply In_singleton.
    assert (~ x ⊥ -> x (⬦ ⊥) -> (forall th, Theory AdAxIdb th -> ((Singleton _ AllForm) th <-> (fun y => forall C, x (Box C) -> y C) th))).
    intros. exfalso ; auto.
    assert (~ x ⊥ -> ~ x (⬦ ⊥) ->
      exists A, ~ x (⬦ A) /\ (forall th, Theory AdAxIdb th -> ((Singleton _ AllForm) th <-> (fun y => (forall C, x (Box C) -> y C) /\ ~ y A) th))).
    intros. exfalso ; auto.
    pose (Build_Psegment x (Singleton _ AllForm) H2 H3 H4 H5 H6).
    exists p. split ; auto. apply IHψ. auto. }
  { destruct (LEM (x (⬦ ⊥))) as [P0 | NP0].
    { remember (fun y => Theory AdAxIdb y /\ (forall C, x (Box C) -> y C)) as U.
      assert (forall th : Ensemble form, th = x \/ U th -> closed AdAxIdb th).
      intros. destruct H2 ; subst ; auto. apply (@segClosed v) ; auto. destruct H2 ; destruct H2 ; auto.
      assert (forall th : Ensemble form, th = x \/ U th -> prime th).
      intros. destruct H3 ; subst ; auto. eapply (@segPrime v) ; auto. destruct H3 ; destruct H3 ; auto.
      assert (x ⊥ -> (forall th, U th <-> th = AllForm)).
      intros. exfalso ; auto.
      assert (~ x ⊥ -> x (⬦ ⊥) -> (forall th, Theory AdAxIdb th -> (U th <-> (fun y => forall C, x (Box C) -> y C) th))).
      intros. split ; subst ; firstorder.
      assert (~ x ⊥ -> ~ x (⬦ ⊥) ->
        exists A, ~ x (⬦ A) /\ (forall th, Theory AdAxIdb th -> (U th <-> (fun y => (forall C, x (Box C) -> y C) /\ ~ y A) th))).
      intros. exfalso ; auto.
      pose (Build_Psegment x U H2 H3 H4 H5 H6).
      exists p. split ; auto. apply IHψ. auto. }
    { remember (fun y => Theory AdAxIdb y /\ (forall C, x (Box C) -> y C) /\ ~ y ⊥) as UBot.
      assert (forall th : Ensemble form, th = x \/ UBot th -> closed AdAxIdb th).
      intros. destruct H2 ; subst ; auto. apply (@segClosed v) ; auto. destruct H2 ; destruct H2 ; auto.
      assert (forall th : Ensemble form, th = x \/ UBot th -> prime th).
      intros. destruct H3 ; subst ; auto. eapply (@segPrime v) ; auto. destruct H3 ; destruct H3 ; auto.
      assert (x ⊥ -> (forall th, UBot th <-> th = AllForm)).
      intros. exfalso ; auto.
      assert (~ x ⊥ -> x (⬦ ⊥) -> (forall th, Theory AdAxIdb th -> (UBot th <-> (fun y => forall C, x (Box C) -> y C) th))).
      intros. exfalso ; auto.
      assert (~ x ⊥ -> ~ x (⬦ ⊥) ->
        exists A, ~ x (⬦ A) /\ (forall th, Theory AdAxIdb th -> (UBot th <-> (fun y => (forall C, x (Box C) -> y C) /\ ~ y A) th))).
      intros. exists Bot ; split ; auto. intros. subst. firstorder.
      pose (Build_Psegment x UBot H2 H3 H4 H5 H6).
      exists p. split ; auto. apply IHψ. auto. } }
Qed.

(* The canonical frames satisfies the sufficient condition of the axiom Idb. *)

Lemma CF_suff_Idb : suff_Idb_frame CF.
Proof.
intros x y z mxy iyz.
destruct (LEM (z = expl)) as [P | NP]; subst.
*** exists expl. repeat split.
  intros w Hw ; unfold In in *. destruct Hw. destruct H. inversion H ; subst. apply ireach_expl in H0 ; subst.
  exists expl. repeat split ; auto. exists expl. repeat split.

*** assert (~ pair_extCKH_prv AdAxIdb (Union _ (@head x) (fun A => exists B, A = Diam B /\ (@head z) B))
    (fun A => exists B, A = Box B /\ ~ (@head z) B)).
{ intro. destruct H as (l0 & H0 & H1). destruct (list_Box_map_repr l0) as [ l1 H2]. intros ; firstorder. subst.
  apply MP with (B:= Box (list_disj l1)) in H1. 2: apply list_disj_Box_obj.
  apply partial_finite in H1. destruct H1 as (l2 & H1 & H2).
  apply prv_list_left_conj in H2. destruct (list_Diam_map_repr l2) as [ l3 H3]. intros ; firstorder. subst.
  apply extCKH_Deduction_Theorem in H2.
  assert (extCKH_prv AdAxIdb (@head x) (☐ list_conj l3 --> list_disj l1)).
  eapply MP. apply Ax ; right ; right ; eexists ; eexists ; reflexivity.
  eapply MP. eapply MP. apply Imp_trans. apply list_conj_Diam_obj. auto.
  apply (@segClosed x) in H ; auto. apply boxreflect with (A:=list_conj l3 --> list_disj l1) in mxy ; auto.
  apply iyz in mxy. assert (In form (@head z) (list_disj l1)).
  apply (@segClosed z) ; auto. eapply MP. apply Id ; exact mxy.
  apply forall_list_conj. intros. apply Id ; auto. unfold In. destruct (H1 (⬦ B)). apply in_map_iff ; eexists ; auto.
  destruct H4 ; subst. inversion H4 ; subst. auto.
  apply prime_list_disj in H3 ; auto. destruct H3 as (A & H4 & H5). destruct H4 ; subst.
  destruct (H0 (☐ A)). apply in_map_iff ; eexists ; auto. destruct H4. inversion H4 ; subst. auto.
  apply NP. apply ireach_expl. intros A HA. apply (@segClosed z) ; auto.
  eapply MP. apply EFQ. apply Id ; auto. apply (@segPrime z) ; auto. }
apply Lindenbaum_pair with (Γ:=AllForm) in H.
2-3: intros C HC ; left ; apply Incl_Set_ClosSubform ; unfold In ; unfold AllForm ; auto.
destruct H as (Δ & J0 & J1 & J2 & J3 & J4).
destruct (LEM (Δ (⬦ Bot))).
- remember (fun y => Theory AdAxIdb y /\ (forall C, Δ (Box C) -> y C)) as U.
  assert (forall th : Ensemble form, th = Δ \/ U th -> closed AdAxIdb th).
  intros. destruct H0 ; subst ; auto. intros C HC ; apply J2 ; auto.
  left ; apply Incl_Set_ClosSubform ; unfold In ; unfold AllForm ; auto. destruct H0 ; destruct H0 ; auto.
  assert (forall th : Ensemble form, th = Δ \/ U th -> prime th).
  intros. destruct H1 ; subst ; auto. apply LEM_prime ; auto. destruct H1 ; destruct H1 ; auto.
  assert (Δ ⊥ -> (forall th, U th <-> th = AllForm)).
  intros. exfalso. apply J4. exists [] ; cbn ; repeat split ; auto. intros. inversion H3. apply Id ; auto.
  assert (~ Δ ⊥ -> Δ (⬦ ⊥) -> (forall th, Theory AdAxIdb th -> (U th <-> (fun y => forall C, Δ (Box C) -> y C) th))).
  intros. split ; intros ; subst ; firstorder.
  assert (~ Δ ⊥ -> ~ Δ (⬦ ⊥) ->
    exists A, ~ Δ (⬦ A) /\ (forall th, Theory AdAxIdb th -> (U th <-> (fun y => (forall C, Δ (Box C) -> y C) /\ ~ y A) th))).
  intros. exfalso ; auto.
  pose (Build_Psegment Δ U H0 H1 H2 H3 H4).
  exists p. repeat split ; auto.
  + intros A HA. unfold head in * ; cbn. apply J0. left. auto.
  + intros s Hs. unfold In in *. destruct Hs. destruct H5. inversion H5 ; subst.
     exists expl. split. exists z. repeat split ; auto.
     destruct (diamwitness s Bot). apply H6 ; auto. destruct H7.
     unfold mreachable ; cbn ; unfold cmreach.
     assert (x0 = (@head expl)). apply Extensionality_Ensembles ; split ; intros A HA ;
     unfold In in *. unfold head ; cbn ; unfold expl ; unfold AllForm ; auto.
     apply (@segClosed s) ; auto. eapply MP. apply EFQ. apply Id ; auto.
     subst ; auto.
  + apply (@segP_noBot_DiamBot p) ; auto.
     intro H5. apply J4. exists [] ; cbn. repeat split ; auto. intros A F ; inversion F. apply Id ; auto.
     split ; [apply (@segClosed z) | apply (@segPrime z)] ; auto.
     intros. destruct (LEM ((@head z) C)) ; auto. exfalso. apply J4.
     exists [Box C]. cbn ; repeat split ; auto. intros. destruct H7 ; subst ; auto. exists C ; split ; auto.
     inversion H7. eapply MP. apply Ax ; left ; left ; eapply IA3 ; reflexivity.
     apply Id ; auto.
- remember (fun x => Theory AdAxIdb x /\ (forall C, Δ (Box C) -> x C) /\ ~ x ⊥) as UBot.
  (* Need to create the UBot-tail of head. *)
  pose (Lindenbaum_Psegment_Diam ⊥ Δ). destruct e as (p & Hp0 & Hp1) ; subst ; auto.
  split. intros C HC ; apply J2 ; auto. left ; apply Incl_Set_ClosSubform ; unfold In ; unfold AllForm ; auto.
  apply LEM_prime ; auto.
  exists p. repeat split ; auto.
  + intros A HA. unfold head in * ; cbn. apply J0. left. auto.
  + intros s Hs. unfold In in *. destruct Hs. destruct H0. inversion H0 ; subst.
     destruct (LEM ((@head s) ⊥)).
     * exists expl ; repeat split ; auto. exists z ; repeat split. apply (@segP_Bot s) ; auto.
     * destruct (LEM ((@head s) (⬦ ⊥))).
       { exists expl ; repeat split ; auto. exists z ; repeat split. apply (@segP_noBot_DiamBot s) ; auto. apply Theory_AllForm.
         unfold head. intros C HC ; unfold expl ; cbn ; unfold AllForm ; auto. }
       { destruct (@segP_noBot_noDiamBot s H2 H3) as (A & K0 & K1).
         assert (~ extCKH_prv AdAxIdb (Union _ (fun B => (@head s) (Box B))  (@head z)) A).
        { intro. apply partial_finite in H4. destruct H4 as (l & G1 & G2). apply prv_list_left_conj in G2.
          apply extCKH_Deduction_Theorem in G2. apply K_rule in G2. apply K0.
          apply (@segClosed s) ; auto. eapply MP. eapply MP. apply Ax ; left ; right ; eapply Kd ; reflexivity.
          apply (extCKH_monot _ _ _ G2). intros B HB. destruct HB. destruct H4. subst. auto.
          apply Id. apply H1. apply J0. right. unfold In. exists (list_conj l). split ; auto.
          apply (@segClosed z) ; auto. apply forall_list_conj. intros. apply Id. apply G1. auto. }
    apply Lindenbaum_Psegment in H4. destruct H4 as (k & F0 & F1). exists k. split ; auto.
    exists z. split. apply In_singleton. intros B HB. unfold In in * ; unfold head in *. apply F0 ; right ; auto.
    apply K1. split ; [apply (@segClosed k) | apply (@segPrime k)] ; auto.
    split ; auto. intros. apply F0. left ; auto. }
  + subst. unfold mreachable. cbn. apply Hp1.
     split ; [apply (@segClosed z) | apply (@segPrime z)] ; auto. split.
     intros. destruct (LEM ((@head z) C)) ; auto. exfalso. apply J4.
     exists [Box C]. cbn ; repeat split ; auto. intros. destruct H2 ; subst ; auto ; try contradiction. exists C ; split ; auto.
     eapply MP. apply Ax ; left ; left ; eapply IA3 ; reflexivity.
     apply Id ; auto.
     intro. apply NP. apply Psegment_prf_irrel. apply Extensionality_Ensembles.
     split ; intros A HA ; unfold head in *. unfold expl ; cbn ; unfold AllForm ; auto.
     apply (@segClosed z) ; auto. eapply MP. apply EFQ. apply Id ; auto.
     unfold tail ; cbn. apply Extensionality_Ensembles. split ; intros A HA.
     apply (@segP_Bot z H0) in HA. subst. apply In_singleton.
     apply (@segP_Bot z H0). inversion HA ; subst ; auto.
Qed.

(* As a consequence, the canonical frames satisfies the correspondent of the axiom Idb. *)

Lemma CF_Idb : Idb_frame CF.
Proof.
apply suff_impl_Idb. apply CF_suff_Idb.
Qed.

(* We leverage the truth lemma to prove a general completeness result parametrised
    in a set of additional axioms validated by a certain class of frames. Completeness
    on this class of frame follows. *)

Variable ClassF : frame -> Prop.
Hypothesis ClassF_AdAx : forall f, ClassF f -> (forall A, AdAxIdb A -> fvalid f A).
Hypothesis CF_ClassF : ClassF CF.

Theorem QuasiCompleteness : forall Γ φ,
    ~ extCKH_prv AdAxIdb Γ φ -> ~ loc_conseq ClassF Γ φ.
Proof.
intros Γ φ D H.
apply Lindenbaum_Psegment in D ; auto.
destruct D as (w & H1 & H2).
assert ((forall A, Γ A -> forces CM w A)). intros. apply truth_lemma. apply H1 ; auto.
apply H2. apply truth_lemma ; auto.
Qed.

Theorem Strong_Completeness : forall Γ φ,
    loc_conseq ClassF Γ φ -> extCKH_prv AdAxIdb Γ φ.
Proof.
intros Γ φ LC. pose (QuasiCompleteness Γ φ).
destruct (LEM (extCKH_prv AdAxIdb Γ φ)) ; auto. exfalso.
apply n ; auto.
Qed.

End general_segP_completeness.


