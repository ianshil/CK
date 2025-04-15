Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.


Axiom LEM : forall P, P \/ ~ P.

Section general_segAB_completeness.


Variable AdAx : form -> Prop.

Definition AdAxCd := fun x => AdAx x \/ (exists A B, (Cd A B) = x).


(* We construct the AB-segments for our canonical model *)

Class ABsegment : Type :=
  { head : @Ensemble form ;
    tail : @Ensemble (@Ensemble form) ;

    (* head and tail are closed under deduction *)
    segClosed : forall th, (th = head \/ tail th) -> closed AdAxCd th ;
    (* head and tail of the ABsegment are quasi-prime *)
    segPrime : forall th, (th = head \/ tail th) -> prime th ;

    (* The ABsegment is A or B *)
    segAorB : (forall th, Theory AdAxCd th -> (tail th <-> (forall C, (head (□ C) -> th C) /\ (th C -> head (◊ C))))) (*A*) \/
                    (forall th, Theory AdAxCd th -> (tail th <-> (forall C, (head (□ C) -> th C)))) (*B*) ;
  }.

(* These AB-segments are segments as they satisfy the two following properties. *)

Lemma boxreflect : forall seg A, (@head seg) (□ A) -> forall th, (@tail seg) th -> th A.
Proof.
intros. destruct segAorB.
(* A *)
- rewrite H1 in H0. apply H0 ; auto. split ; [apply segClosed | apply segPrime] ; auto.
(* B *)
- rewrite H1 in H0. apply H0 ; auto. split ; [apply segClosed | apply segPrime] ; auto.
Qed.

Lemma diamwitness : forall seg A, (@head seg) (◊ A) -> exists th, (@tail seg) th /\ th A.
Proof.
intros. destruct segAorB.
(* A *)
- destruct (LEM (head (◊ ⊥))).
  + exists AllForm. split. 2: unfold AllForm ; auto. apply H0. apply Theory_AllForm.
     intro C ; split ; intro HC.
     unfold AllForm ; auto. apply segClosed ; auto. eapply MP. eapply MP.
     apply Ax ; left ; right ; eapply Kd ; reflexivity. apply Nec. apply EFQ. apply Id ; auto.
  + assert (~ pair_extCKH_prv AdAxCd (Union _ (fun x => exists B, head (Box B) /\ x = B) (Singleton _ A)) (fun y => exists B, y = B /\ ~ head (◊ B))).
     { intro. destruct H2 as (l & H2 & H3). destruct l.
     * apply H1. apply segClosed ; auto.
       eapply MP. 2: apply Id ; exact H. eapply MP. apply Ax ; left ; right ; eapply Kd ; reflexivity.
       apply extCKH_Deduction_Theorem in H3. apply K_rule in H3. apply (extCKH_monot _ _ _ H3).
       intros C HC. destruct HC as (D & (E & K2 & K3) & K1) ; subst ; auto.
     * remember (f :: l) as l'. apply extCKH_Deduction_Theorem in H3. apply K_rule in H3.
       apply MP with (B:=(◊ A) → (◊ list_disj l')) in H3. apply extCKH_Detachment_Theorem in H3.
       apply Diam_distrib_list_disj in H3. apply extCKH_monot with (Γ1:=head) in H3.
       apply segClosed in H3 ; auto. apply prime_list_disj in H3 ; auto. destruct H3 as (C & H4 & H5) ; subst.
       destruct H4 ; subst. apply in_map_iff in H3. destruct H3 as (D & K0 & K1) ; subst. apply H2 in K1.
       destruct K1 ; auto. destruct H3 ; subst ; auto. apply H1. apply segClosed ; auto. eapply MP.
       apply EFQ. apply Id ; auto. apply segPrime ; auto.
       intros B HB. inversion HB ; subst. destruct H4. destruct H4 ; subst. destruct H4. destruct H4 ; subst ; auto.
       inversion H4 ; subst ; auto. subst ; intro H4 ; inversion H4.
       apply Ax ; left ; right ; eapply Kd ; reflexivity. }
   apply (Lindenbaum_pair _ AllForm) in H2.
   destruct H2 as (Δm & G0 & G1 & G2 & G3 & G4). exists Δm. split ; auto.
   apply H0. split ; [intros B HB ; apply G2 ; unfold AllForm ; auto | apply LEM_prime ; auto].
   left. apply Incl_Set_ClosSubform ; unfold In ; auto.
   intro C ; split ; intro HC. apply G0. left ; exists C ; split ; auto.
   destruct (LEM (head (◊ C))) ; auto. exfalso. apply G4. exists [C]. split ; auto.
   intros. exists C ; split ; auto. inversion H3 ; subst ; auto. inversion H4.
   cbn. eapply MP. apply Ax ; left;  left ; eapply IA3 ; reflexivity. apply Id ; auto.
   apply G0. right ; apply In_singleton.
   all: intros C HC ; left ; apply Incl_Set_ClosSubform ; unfold AllForm ; unfold In ; auto.
(* B *)
- exists AllForm. split ; cbn ; auto.
  apply H0. apply Theory_AllForm.
  intros. all: unfold AllForm ; auto.
Qed.

(* We admit that the proofs of the properties of AB-segments are
    irrelevant to the identity between ABsegments. *)

Axiom ABsegment_prf_irrel : forall (s0 s1 : ABsegment),
                (@head s0) = (@head s1) ->
                (@tail s0) = (@tail s1) ->
                s0 = s1.

(* Exploding world of the canonical model. *)

Lemma cexpl_segClosed : forall th, (th = AllForm \/ (Singleton _ AllForm) th) ->  closed AdAxCd th.
Proof.
intros. destruct H ; subst ; intros A HA ; auto. unfold AllForm ; auto.
inversion H ; subst ; auto. unfold AllForm ; auto.
Qed.

Lemma cexpl_segPrime : forall th, (th = AllForm \/ (Singleton _ AllForm) th) -> prime th.
Proof.
intros. destruct H ; subst ; intros A B H0 ; left ; unfold AllForm ; auto ; inversion H ; unfold AllForm ; auto.
Qed.

Lemma cexpl_segAorB : (forall th, Theory AdAxCd th -> ((Singleton _ AllForm) th <-> (forall C, (AllForm (□ C) -> th C) /\ (th C -> AllForm (◊ C))))) \/
                    (forall th, Theory AdAxCd th -> ((Singleton _ AllForm) th <-> (forall C, (AllForm (□ C) -> th C)))).
Proof.
right. intros. split ; intros.
- inversion H0 ; subst ; unfold AllForm ; auto.
- enough (AllForm = th). subst ; apply In_singleton.
  apply Extensionality_Ensembles. split ; intros C HC.
  apply H. apply Id. apply H0. unfold AllForm ; auto. unfold In ; unfold AllForm ; auto.
Qed.


Instance cexpl : ABsegment :=
  {| head := AllForm ;
    tail := Singleton _ AllForm ;

    segClosed := cexpl_segClosed ;
    segPrime := cexpl_segPrime ;

    segAorB := cexpl_segAorB

  |}.

(* Intuitionistic relation on the canonical model. *)

Definition cireach (s0 s1 : ABsegment) : Prop :=
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
    assert ((@head u) (◊ ⊥)). rewrite H0. unfold head. unfold cexpl. unfold AllForm. auto.
    pose (diamwitness _ _ H1). destruct e. destruct H2.
    assert (x = AllForm). apply Extensionality_Ensembles.
    split ; intros A HA ; auto. unfold In ; unfold AllForm ; auto.
    apply segClosed ; auto. eapply MP. apply EFQ. apply Id ; auto. subst. auto. }
apply ABsegment_prf_irrel ; auto.
Qed.

(* Modal relation *)

Definition cmreach (s0 s1 : ABsegment) : Prop :=
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
      assert ((@head u) (◊ ⊥)). rewrite H0. unfold head. unfold cexpl. unfold AllForm. auto.
      pose (diamwitness _ _ H1). destruct e. destruct H2.
      assert (x = AllForm). apply Extensionality_Ensembles.
      split ; intros A HA ; auto. unfold In ; unfold AllForm ; auto.
      apply segClosed ; auto. eapply MP. apply EFQ. apply Id ; auto. subst. auto. }
  apply ABsegment_prf_irrel ; auto.
- unfold cmreach. unfold tail. unfold head. unfold cexpl. apply In_singleton.
Qed.

(* We can define the canonical frame. *)

Instance CF : frame :=
      {|
        nodes := ABsegment ;
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

Lemma Lindenbaum_ABsegment ψ Δ :
  ~ extCKH_prv AdAxCd Δ ψ ->
  exists w : ABsegment, Included _ Δ head /\ ~ In _ head ψ.
Proof.
  intros H1.
  assert (J0: In form (Clos AllForm) ψ). left. apply Incl_Set_ClosSubform ; unfold In ; unfold AllForm ; auto.
  assert (J1: Included _ Δ (Clos AllForm)). intros C HC. left ; apply Incl_Set_ClosSubform ; unfold In ; unfold AllForm ; auto.
  pose (Lindenbaum _ _ _ _ J0 J1 H1).
  destruct s as (Δm & H2 & H3 & H4 & H5 & H6).
  pose (Build_ABsegment Δm (fun th => Theory AdAxCd th /\ (forall C, (Δm (□ C) -> th C) /\ (th C -> Δm (◊ C))))); intros.
  eexists (a _ _ _) ; split ; auto. intro. apply H6. apply Id ; auto.
  Unshelve. all: intros ; auto.
  - destruct H ; subst ; auto. intros C HC ; apply H4 ; auto.
    left ; apply Incl_Set_ClosSubform ; unfold In ; unfold AllForm ; auto.
    destruct H. intros C HC ; apply H ; auto.
  - destruct H ; subst ; auto. apply LEM_prime ; auto. destruct H ; destruct H ; auto.
  - left. intros. split ; intros.
    + split ; intros. apply H0 ; auto. apply H0 ; auto.
    + split ; auto.
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

Lemma truth_lemma : forall ψ (s : ABsegment),
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
      assert ((@head s) (◊ ⊥)). rewrite H. unfold head. unfold cexpl. unfold AllForm. auto.
      pose (diamwitness _ _ H1). destruct e. destruct H2.
      assert (x = AllForm). apply Extensionality_Ensembles.
      split ; intros A HA ; auto. unfold In ; unfold AllForm ; auto.
      apply segClosed ; auto. eapply MP. apply EFQ. apply Id ; auto. subst. auto. }
  apply ABsegment_prf_irrel ; auto.
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
- destruct (LEM (head (ψ1 → ψ2))) ; auto. exfalso.
  assert (~ extCKH_prv AdAxCd (Union _ head (Singleton _ ψ1)) ψ2).
  intro. apply extCKH_Deduction_Theorem in H1. apply H. apply segClosed ; auto.
  assert (Included form (Union _ head (Singleton form ψ1)) (Clos AllForm)).
  intros A HA. left. apply Incl_Set_ClosSubform ; unfold In ; unfold AllForm ; auto.
  pose (Lindenbaum_ABsegment _ _ H1). destruct e as [w [Hw1 Hw2]].
  assert (J2: cireach s w). unfold cireach.
  intros A HA. apply Hw1. apply Union_introl. auto. simpl in H0.
  pose (H0 _ J2). apply Hw2. apply IHψ2 ; auto. apply f. apply IHψ1 ; auto.
  apply segClosed ; auto. apply Id. apply Hw1.
  apply Union_intror ; apply In_singleton.
- intros.
  apply IHψ1 in H1 ; auto. unfold cireach in H. apply H in H0.
  apply IHψ2 ; auto.
  assert (extCKH_prv AdAxCd head ψ2). eapply MP. apply Id ; exact H0.
  apply Id ; auto. apply segClosed ; auto.
(* Box ψ *)
- destruct (LEM (head (□ ψ))) ; auto. exfalso.
  assert (~ extCKH_prv AdAxCd (fun x => exists A, (@head s) (□ A) /\ x = A) ψ).
  intro. apply H. apply segClosed ; auto. apply K_rule in H1.
  apply (extCKH_monot _ _ _ H1). intros B HB. unfold In in *.
  destruct HB as (C & (D & HD0 & HD1) & HC) ; subst ; auto.
  apply Lindenbaum with (Γ:=AllForm) in H1 ; auto.
  2: unfold In ; left ; apply Incl_Set_ClosSubform ; unfold In ; unfold AllForm ; auto.
  2: intros C HC ; unfold In ; left ; apply Incl_Set_ClosSubform ; unfold In ; unfold AllForm ; auto.
  destruct H1 as (Γ0 & J0 & J1 & J2 & J3 & J4).
  (* Need to create the B-tail of head. *)
  assert (forall th : Ensemble form, th = head \/ (fun x => Theory AdAxCd x /\ (forall C, head (□ C) -> x C)) th -> closed AdAxCd th).
  intros. destruct H1 ; subst ; auto. apply (@segClosed s) ; auto. destruct H1 ; destruct H1 ; auto.
  assert (forall th : Ensemble form, th = head \/ (fun x => Theory AdAxCd x /\ (forall C, head (□ C) -> x C)) th -> prime th).
  intros. destruct H2 ; subst ; auto. eapply (@segPrime s) ; auto. destruct H2 ; destruct H2 ; auto.
  assert ((forall th, Theory AdAxCd th -> ((fun x => Theory AdAxCd x /\ (forall C, head (□ C) -> x C)) th <-> (forall C, (head (□ C) -> th C) /\ (th C -> head (◊ C))))) \/
                    (forall th, Theory AdAxCd th -> ((fun x => Theory AdAxCd x /\ (forall C, head (□ C) -> x C)) th <-> (forall C, (head (□ C) -> th C))))).
  right. intros ; split ; intros ; auto. apply H4 ; auto.
  pose (Build_ABsegment head (fun x => Theory AdAxCd x /\ (forall C, head (□ C) -> x C)) H1 H2 H3).
  assert (cireach s a). intros C HC ; auto.
  (* Need to create the B-tail of Γ0 *)
  assert (forall th : Ensemble form, th = Γ0 \/ (fun x => Theory AdAxCd x /\ (forall C, Γ0 (□ C) -> x C)) th -> closed AdAxCd th).
  intros. destruct H5 ; subst ; auto. intros A HA ; apply J2 ; auto. left ; apply Incl_Set_ClosSubform ; unfold In ; unfold AllForm ; auto.
  destruct H5 ; destruct H5 ; auto.
  assert (forall th : Ensemble form, th = Γ0 \/ (fun x => Theory AdAxCd x /\ (forall C, Γ0 (□ C) -> x C)) th -> prime th).
  intros. destruct H6 ; subst ; auto. apply LEM_prime ; auto. destruct H6 ; destruct H6 ; auto.
  assert ((forall th, Theory AdAxCd th -> ((fun x => Theory AdAxCd x /\ (forall C, Γ0 (□ C) -> x C)) th <-> (forall C, (Γ0 (□ C) -> th C) /\ (th C -> Γ0 (◊ C))))) \/
                    (forall th, Theory AdAxCd th -> ((fun x => Theory AdAxCd x /\ (forall C, Γ0 (□ C) -> x C)) th <-> (forall C, (Γ0 (□ C) -> th C))))).
  right. intros ; split ; intros ; auto. apply H8 ; auto.
  pose (Build_ABsegment Γ0 (fun x => Theory AdAxCd x /\ (forall C, Γ0 (□ C) -> x C)) H5 H6 H7).
  apply H0 with (u:=a0) in H4. apply IHψ in H4 ; auto. apply J4. apply Id. auto.
  unfold cmreach. unfold tail. unfold head. cbn. repeat split ; auto. intros. apply J0. exists C ; split ; auto.
- intros. apply IHψ ; auto. apply H in H0. pose (boxreflect _ _ H0). apply p ; auto.
(* Diam ψ *)
- destruct (LEM (head (◊ ψ))) ; auto. exfalso.
  assert (forall th : Ensemble form, th = head \/ (fun x => Theory AdAxCd x /\ (forall C, (head (□ C) -> x C) /\ (x C -> head (◊ C)))) th -> closed AdAxCd th).
  intros. destruct H1 ; subst ; auto. apply (@segClosed s) ; auto. destruct H1 ; destruct H1 ; auto.
  assert (forall th : Ensemble form, th = head \/ (fun x => Theory AdAxCd x /\ (forall C, (head (□ C) -> x C) /\ (x C -> head (◊ C)))) th -> prime th).
  intros. destruct H2 ; subst ; auto. eapply (@segPrime s) ; auto. destruct H2 ; destruct H2 ; auto.
  assert ((forall th, Theory AdAxCd th -> ((fun x => Theory AdAxCd x /\ (forall C, (head (□ C) -> x C) /\ (x C -> head (◊ C)))) th <-> (forall C, (head (□ C) -> th C) /\ (th C -> head (◊ C))))) \/
                    (forall th, Theory AdAxCd th -> ((fun x => Theory AdAxCd x /\ (forall C, (head (□ C) -> x C) /\ (x C -> head (◊ C)))) th <-> (forall C, (head (□ C) -> th C))))).
  left. intros ; split ; intros ; auto. apply H4 ; auto.
  pose (Build_ABsegment head (fun x => Theory AdAxCd x /\ (forall C, (head (□ C) -> x C) /\ (x C -> head (◊ C)))) H1 H2 H3).
  assert (cireach s a). intros C HC ; auto.
  apply H0 in H4. destruct H4. destruct H4. apply IHψ in H5.
  unfold head in H5. apply H4 in H5. auto.
- intros. unfold cireach in H. apply H in H0.
  apply diamwitness in H0. destruct H0. destruct H0.
  assert (forall th : Ensemble form, th = x \/ (fun y => Theory AdAxCd y /\ (forall C, x (□ C) -> y C)) th -> closed AdAxCd th).
  intros. destruct H2 ; subst ; auto. apply (@segClosed  _ x) ; auto. inversion H2. intros C HC ; auto. apply H3 ; auto.
  assert (forall th : Ensemble form, th = x \/ (fun y => Theory AdAxCd y /\ (forall C, x (□ C) -> y C)) th -> prime th).
  intros. destruct H3 ; subst ; auto. eapply (@segPrime _ x) ; auto. destruct H3 ; destruct H3 ; auto.
  assert ((forall th, Theory AdAxCd th -> ((fun y => Theory AdAxCd y /\ (forall C, x (□ C) -> y C)) th <-> (forall C, (x (□ C) -> th C) /\ (th C -> x (◊ C))))) \/
                    (forall th, Theory AdAxCd th -> ((fun y => Theory AdAxCd y /\ (forall C, x (□ C) -> y C)) th <-> (forall C, (x (□ C) -> th C))))).
  right. intros ; split ; intros ; auto. apply H5 ; auto.
  pose (Build_ABsegment x (fun y => Theory AdAxCd y /\ (forall C, x (□ C) -> y C)) H2 H3 H4).
  exists a. split ; auto. apply IHψ ; auto.
Qed.

(* The canonical frames satisfies the sufficient condition of the axiom Cd. *)

Lemma CF_suff_Cd : suff_Cd_frame CF.
Proof.
intro x.
(* We create the A-segment in the cluster of x (it could be x, but we want to make sure). *)
assert (forall th : Ensemble form, th = (@head x) \/ (fun w => Theory AdAxCd w /\ (forall C, ((@head x)  (□ C) -> w C) /\ (w C -> (@head  x) (◊ C)))) th -> closed AdAxCd th).
intros. destruct H ; subst ; auto. apply (@segClosed  x) ; auto. destruct H ; destruct H ; auto.
assert (forall th : Ensemble form, th = (@head  x) \/ (fun w => Theory AdAxCd w /\ (forall C, ((@head  x)  (□ C) -> w C) /\ (w C -> (@head  x) (◊ C)))) th -> prime th).
intros. destruct H0 ; subst ; auto. eapply (@segPrime x) ; auto. destruct H0 ; destruct H0 ; auto.
assert ((forall th, Theory AdAxCd th -> ((fun w => Theory AdAxCd w /\ (forall C, ((@head  x)  (□ C) -> w C) /\ (w C -> (@head  x) (◊ C)))) th <-> (forall C, ((@head  x) (□ C) -> th C) /\ (th C -> (@head  x) (◊ C))))) \/
                  (forall th, Theory AdAxCd th -> ((fun w => Theory AdAxCd w /\ (forall C, ((@head  x)  (□ C) -> w C) /\ (w C -> (@head  x) (◊ C)))) th <-> (forall C, ((@head  x) (□ C) -> th C))))).
left. intros ; split ; intros ; auto. apply H2 ; auto.
pose (Build_ABsegment _ _ H H0 H1).
exists a. repeat split ; auto.
- intros A HA ; auto.
- intros y z ixy maz.
  destruct (LEM (mreachable y cexpl)) as [P | NP].
  { exists cexpl. split ; auto. intros A HA. unfold In ; unfold head ; unfold cexpl ; unfold AllForm ; auto. }
  { assert (~ pair_extCKH_prv AdAxCd (Union _ (fun B => (@head  y) (□ B)) (@head  z)) (fun B => ~ (@head  y) (◊ B))).
  { intro. destruct H2 as (l & G0 & G1). destruct (partial_finite _ _ _ _ G1) as (l0 & G2 & G3).
    apply prv_list_left_conj in G3. apply extCKH_Deduction_Theorem in G3. apply K_rule in G3.
    apply MP with (B:=(◊ list_conj l0) → (◊list_disj l)) in G3.
    apply extCKH_monot with (Γ1:= (@head  y)) in G3. apply extCKH_Detachment_Theorem in G3.
    apply extCKH_monot with (Γ1:= (@head  y)) in G3.
    destruct l.
    { cbn in G3. apply (@segClosed  y) in G3 ; auto. apply NP. apply diamwitness in G3. destruct G3. destruct H2.
      unfold mreachable ; cbn. unfold cmreach. enough (x0 = (@head cexpl)). subst ; auto.
      apply Extensionality_Ensembles ; split ; intros A HA. unfold In ; unfold head ; unfold cexpl ; unfold AllForm ; auto.
      apply (@segClosed y) ; auto. eapply MP. apply EFQ. apply Id ; auto. }
    { apply Diam_distrib_list_disj in G3. apply (@segClosed  y) in G3. apply prime_list_disj in G3 ; auto.
      destruct G3 as (C & F0 & F1). destruct F0 ; subst. apply in_map_iff in H2. destruct H2 as (D & F2 & F3) ; subst.
      apply G0 with D ; auto. apply G0 with f ; cbn ; auto. apply (@segClosed  y) ; auto. eapply MP.
      apply EFQ. apply Id ; auto. intros D R Hor ; apply (@segPrime y) ; auto. auto. intro. inversion H2. }
    intros B HB ; unfold In in * ; unfold head in *. inversion HB ; subst ; auto. inversion H2 ; subst.
    apply ixy. unfold In. assert ((@head  x) = (@head  a)). auto. cbn. rewrite H3.
    apply maz. apply (@segClosed a) ; auto. apply forall_list_conj. intros. apply Id ; auto. apply G2 in H4 ; auto.
    intros B HB ; unfold In in * ; unfold head in *. destruct HB as (C & F0 & F1) ; subst ; auto.
    apply Ax ; left ; right ; eapply Kd ; reflexivity. }
  apply Lindenbaum_pair with (Γ:=AllForm) in H2.
  2-3: intros C HC ; left ; apply Incl_Set_ClosSubform ; unfold In ; unfold AllForm ; auto.
  destruct H2 as (Γ0 & J0 & J1 & J2 & J3 & J4).
  assert (forall th : Ensemble form, th = Γ0 \/ (fun w => Theory AdAxCd w /\ (forall C, (Γ0  (□ C) -> w C) /\ (w C -> Γ0 (◊ C)))) th -> closed AdAxCd th).
  intros. destruct H2 ; subst ; auto. intros B HB. apply J2 ; auto. left ; apply Incl_Set_ClosSubform ; unfold In ; unfold AllForm ; auto.
  destruct H2 ; destruct H2 ; auto.
  assert (forall th : Ensemble form, th = Γ0 \/ (fun w => Theory AdAxCd w /\ (forall C, (Γ0  (□ C) -> w C) /\ (w C -> Γ0 (◊ C)))) th -> prime th).
  intros. destruct H3 ; subst ; auto. apply LEM_prime ; auto. destruct H3 ; destruct H3 ; auto.
  assert ((forall th, Theory AdAxCd th -> ((fun w => Theory AdAxCd w /\ (forall C, (Γ0  (□ C) -> w C) /\ (w C -> Γ0 (◊ C)))) th <-> (forall C, (Γ0 (□ C) -> th C) /\ (th C -> Γ0 (◊ C))))) \/
                    (forall th, Theory AdAxCd th -> ((fun w => Theory AdAxCd w /\ (forall C, (Γ0 (□ C) -> w C) /\ (w C -> Γ0 (◊ C)))) th <-> (forall C, (Γ0 (□ C) -> th C))))).
  left. intros ; split ; intros ; auto. destruct H5 ; auto.
  pose (Build_ABsegment _ _ H2 H3 H4).
  exists a0. repeat split.
  + unfold mreachable ; cbn. unfold cmreach ; cbn. auto. pose (@segAorB y). destruct o.
     apply H5 ; auto. split ; auto. intro C ; split ; intro HC ; auto. apply J0 ; left ; auto.
     destruct (LEM ((@head y) (◊ C))) ; auto.
     exfalso. apply J4. exists [C]. split ; intros. inversion H7 ; subst ; auto.
     cbn. eapply MP. apply Ax ; left ; left ; eapply IA3 ; reflexivity. apply Id. auto.
     apply H5 ; auto. split ; auto. intros C HC ; auto. apply J0 ; left ; auto.
  + intros B HB. unfold In in * ; unfold head in * ; cbn in *. apply J0 ; right ; auto. }
Qed.

Lemma CF_Cd : Cd_frame CF.
Proof.
apply suff_impl_Cd. apply CF_suff_Cd.
Qed.

(* We leverage the truth lemma to prove a general completeness result parametrised
    in a set of additional axioms validated by a certain class of frames. Completeness
    on this class of frame follows. *)

Variable ClassF : frame -> Prop.
Hypothesis ClassF_AdAx : forall f, ClassF f -> (forall A, AdAxCd A -> fvalid f A).
Hypothesis CF_ClassF : ClassF CF.

Theorem QuasiCompleteness : forall Γ φ,
    ~ extCKH_prv AdAxCd Γ φ -> ~ loc_conseq ClassF Γ φ.
Proof.
intros Γ φ D H.
apply Lindenbaum_ABsegment in D ; auto.
destruct D as (w & H1 & H2).
assert ((forall A, Γ A -> forces CM w A)). intros. apply truth_lemma. apply H1 ; auto.
apply H2. apply truth_lemma ; auto.
Qed.

Theorem Strong_Completeness : forall Γ φ,
    loc_conseq ClassF Γ φ -> extCKH_prv AdAxCd Γ φ.
Proof.
intros Γ φ LC. pose (QuasiCompleteness Γ φ).
destruct (LEM (extCKH_prv AdAxCd Γ φ)) ; auto. exfalso.
apply n ; auto.
Qed.

End general_segAB_completeness.


