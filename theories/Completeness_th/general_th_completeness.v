Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.


Axiom LEM : forall P, P \/ ~ P.

Section general_th_completeness.

Variable AdAx : form -> Prop.

Definition AdAxCdIdb := fun x => AdAx x \/ (exists A B, (Cd A B) = x \/ (Idb A B) = x).

(* We first create cworlds of our canonical model. They will act
    as worlds of our model. *)

Class cworld : Type :=
  { th : @Ensemble form ;

    (* th is deductively closed *)
    Closed : closed AdAxCdIdb th ;
    (* th is quasi-prime *)
    Prime : prime th ;
  }.

Axiom cworld_prf_irrel : forall (w v : cworld),
                (@th w) = (@th v) ->
                w = v.

(* Exploding world of the canonical model. *)

Lemma cexpl_Closed : closed AdAxCdIdb AllForm.
Proof.
apply Theory_AllForm.
Qed.

Lemma cexpl_Prime : prime AllForm.
Proof.
apply (@Theory_AllForm AdAxCdIdb).
Qed.

Instance cexpl : cworld :=
  {| th := AllForm ;

    Closed := cexpl_Closed ;
    Prime := cexpl_Prime
  |}.

(* Intuitionistic relation on the canonical model. *)

Definition cireach (P0 P1 : cworld) : Prop :=
  Included _ (@th P0) (@th P1).

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

Lemma cireach_expl u : cireach  cexpl u -> u = cexpl.
Proof.
intros. apply cworld_prf_irrel.
apply Extensionality_Ensembles. split ; intros C HC ; auto.
unfold In in *. unfold th in * ; unfold expl ; cbn ; unfold AllForm ; auto.
Qed.

(* Modal relation *)

Definition cmreach (P0 P1 : cworld) : Prop :=
  (forall A, (@th P0) (□ A) -> (@th P1) A) /\
  (forall A, (@th P1) A -> (@th P0) (◊ A)).

Lemma cmreach_expl  u : cmreach  cexpl u <-> u = cexpl.
Proof.
split ; intro ; subst.
- apply cworld_prf_irrel.
  apply Extensionality_Ensembles. split ; intros A HA ; auto.
  unfold In ; unfold th ; cbn ; unfold AllForm ; auto.
  assert (th Bot). unfold th. apply H. unfold th. unfold th ; unfold cexpl.
  unfold Clos. auto. apply Closed ; auto. eapply MP. apply EFQ. apply Id ; auto.
- unfold cmreach. unfold th. unfold cexpl. split ; intros ; auto.
Qed.

(* We can define the canonical frame. *)

Instance CF : frame :=
      {|
        nodes := cworld ;
        expl:= cexpl ;

        ireachable := cireach ;
        ireach_refl := cireach_refl ;
        ireach_tran := cireach_trans ;
        ireach_expl := cireach_expl  ;

        mreachable := cmreach  ;
        mreach_expl := cmreach_expl  ;
      |}.

(* As expected, we can create canonical worlds using our
   Lindenbaum lemma. *)

Lemma Lindenbaum_cworld ψ Δ :
  ~ pair_extCKH_prv AdAxCdIdb Δ ψ ->
  exists w : cworld, Included _ Δ th /\ Included _ ψ (Complement _ th).
Proof.
  intros.
  assert (J0: Included _ ψ (Clos AllForm)). intros C HC. left ; apply Incl_Set_ClosSubform ; unfold In ; unfold AllForm ; auto.
  assert (J1: Included _ Δ (Clos AllForm)). intros C HC. left ; apply Incl_Set_ClosSubform ; unfold In ; unfold AllForm ; auto.
  pose (Lindenbaum_pair _ _ _ _ J0 J1 H).
  destruct s as (Δm & H2 & H3 & H4 & H5 & H6).
  pose (Build_cworld Δm); intros.
  eexists (c _ _) ; split ; auto. intros A HA J.
  apply H6. exists [A]. split ; auto.
  - intros B HB. inversion HB ; subst ; auto. inversion H0.
  - cbn. eapply MP. apply Ax ; left ; left ; eapply IA3 ; reflexivity.
    apply Id ; auto.
  Unshelve.
  intros A HA ; apply H4 ; auto. left ; apply Incl_Set_ClosSubform ; unfold In ; unfold AllForm ; auto.
  apply LEM_prime ; auto.
Qed.

(* We define the canonical valuation. *)

Definition cval s (p : nat) := (@th s) (# p).

Lemma cval_persist : forall u v, cireach  u v -> forall (p : nat), cval u p -> cval v p.
Proof.
intros. unfold cval in *. apply H. auto.
Qed.

Lemma cval_expl  : forall p, cval cexpl p.
Proof.
intros. unfold cval. unfold head ; unfold cexpl ; cbn ; unfold AllForm ; auto.
Qed.



(* Finally we can define the canonical model. *)

Instance CM : model :=
      {|
        fra := CF ;

        val := cval  ;
        persist :=  cval_persist ;
        val_expl :=  cval_expl
      |}.

(* Then we can prove the truth lemma. *)

Lemma truth_lemma : forall ψ (c : cworld),
  forces CM c ψ <-> (@th c) ψ.
Proof.
induction ψ ; intros c ; split ; intros H0 ; simpl ; try simpl in H1 ; auto.
(* nat *)
- inversion H0. firstorder.
(* Bot *)
- apply cworld_prf_irrel.
  apply Extensionality_Ensembles. split ; intros C HC ; auto.
  * unfold In in *. unfold th in * ; unfold cexpl ; cbn. unfold AllForm ; auto.
  * unfold In in *. apply Closed ; auto. eapply MP.
    apply EFQ. apply Id ; auto.
(* And ψ1 ψ2 *)
- destruct H0. apply IHψ1 in H ; auto. apply IHψ2 in H0 ; auto. apply Closed ; auto.
  eapply MP. eapply MP. eapply MP. apply Ax ; left ; left ; eapply IA8 ; reflexivity.
  apply imp_Id_gen. eapply MP. apply Thm_irrel. 1-2: apply Id ; auto.
- split.
  apply IHψ1 ; auto. apply Closed ; auto. eapply MP.
  apply Ax ; left ; left ; eapply IA6 ; reflexivity. apply Id. exact H0.
  apply IHψ2 ; auto. apply Closed ; auto. eapply MP.
  apply Ax ; left ; left ; eapply IA7 ; reflexivity. apply Id. exact H0.
(* Or ψ1 ψ2 *)
- destruct H0.
  apply IHψ1 in H ; auto. apply Closed ; auto. eapply MP.
  apply Ax ; left ; left ; eapply IA3 ; reflexivity. apply Id. exact H.
  apply IHψ2 in H ; auto. apply Closed ; auto. eapply MP.
  apply Ax ; left ; left ; eapply IA4 ; reflexivity. apply Id. exact H.
- destruct (Prime ψ1 ψ2) ; auto.
  left. apply IHψ1 ; auto.
  right. apply IHψ2 ; auto.
(* Imp ψ1 ψ2 *)
- destruct (LEM (th (ψ1 → ψ2))) ; auto. exfalso.
  assert (~ pair_extCKH_prv AdAxCdIdb (Union _ th (Singleton _ ψ1)) (Singleton _ ψ2)).
  intro. destruct H1 as (l & J0 & J1). apply extCKH_Deduction_Theorem in J1. apply H.
  apply Closed ; auto. eapply MP. eapply MP. apply Imp_trans. exact J1.
  apply extCKH_Deduction_Theorem. apply forall_list_disj with l. apply Id ; right ; apply In_singleton.
  intros. apply J0 in H1. inversion H1 ; subst. apply imp_Id_gen.
  pose (Lindenbaum_cworld _ _ H1). destruct e as [w [Hw1 Hw2]].
  assert (J2: cireach c w). unfold cireach.
  intros A HA. apply Hw1. apply Union_introl. auto. simpl in H0.
  pose (H0 _ J2).
  assert (~ th ψ2). apply Hw2. apply In_singleton. apply H2.
  apply IHψ2 ; auto. apply f. apply IHψ1 ; auto.
  apply Closed ; auto. apply Id. apply Hw1.
  apply Union_intror ; apply In_singleton.
- intros.
  apply IHψ1 in H1 ; auto. unfold cireach in H. apply H in H0.
  apply IHψ2 ; auto.
  assert (extCKH_prv AdAxCdIdb th ψ2). eapply MP. apply Id ; exact H0.
  apply Id ; auto. apply Closed ; auto.
(* Box ψ *)
- destruct (LEM (th (□ ψ))) ; auto. exfalso.
  assert (~ pair_extCKH_prv AdAxCdIdb (fun x => exists A, (@th c) (□ A) /\ x = A) (Singleton _ ψ)).
  { intro. destruct H1 as (l & K0 & K1).
    apply H. apply Closed ; auto. apply forall_list_disj with (A:=ψ) in K1.
    apply K_rule in K1. apply (extCKH_monot _ _ _ K1). intros B HB. unfold In in *.
    destruct HB as (C & (D & HD0 & HD1) & HC) ; subst ; auto.
    intros B HB. apply K0 in HB. inversion HB ; subst. apply imp_Id_gen. }
  pose (Lindenbaum_cworld _ _ H1). destruct e as [w [Hw1 Hw2]].
  assert (~ pair_extCKH_prv AdAxCdIdb (Union _ (@th c) (fun x => exists A, (@th w) A /\ x = ◊ A)) (fun x => exists A, ~ ((@th w) A) /\ x = □ A)).
  { intro. destruct H2 as (l & K0 & K1).
    destruct (list_disj_map_Box l) as (l' & Hl') ; subst. intros. apply K0 in H2. destruct H2. destruct H2 ; subst ; eexists ; auto.
    apply list_disj_Box in K1.
    assert (exists dl, (forall A : form, List.In A dl -> (fun x => exists A, (@th w) A /\ x = ◊ A) A) /\
    extCKH_prv AdAxCdIdb (Union _ (@th c) (Singleton _ (list_conj dl)))  (Box (list_disj l'))).
    destruct (partial_finite _ _ _ _ K1) as (l & G0 & G1). exists l. split ; auto.
    apply prv_list_left_conj ; auto.
    destruct H2 as (dl & K2 & K3).
    apply extCKH_Deduction_Theorem in K3.
    destruct (list_conj_map_Diam dl) as (dl' & Hdl') ; subst.
    intros. apply K2 in H2. destruct H2. destruct H2 ; subst ; eexists ; auto.
    assert (extCKH_prv AdAxCdIdb (@th c) ((◊ list_conj dl') → (□ list_disj l'))).
    eapply MP. eapply MP. apply Imp_trans. apply list_conj_Diam_obj. auto.
    assert (extCKH_prv AdAxCdIdb (@th c) (□ (list_conj dl' → list_disj l'))).
    eapply MP. apply Ax ; right ; right ; eexists ; eexists ; right ; reflexivity. auto.
    assert ((@th w) (list_disj l')). apply Closed. apply MP with (list_conj dl'). apply Id.
    unfold In. apply Hw1. unfold In ; eexists ; split ; auto. apply Closed ; auto.
    apply forall_list_conj. intros. apply Id. destruct (K2 (Diam B)).
    apply in_map ; auto. destruct H5 ; subst ; auto. inversion H6 ; subst ; auto.
    apply prime_list_disj in H4. destruct H4 as (A & [G0 | G0] & G1).
    assert (List.In (Box A) (map Box l')). apply in_map_iff ; exists A ; auto. apply K0 in H4.
    destruct H4 as (B & G2 & G3) ; inversion G3 ; subst. auto.
    subst. assert ((@th w) ψ). apply Closed. eapply MP. apply EFQ. apply Id ; auto.
    assert ((Singleton form ψ) ψ). apply In_singleton. apply Hw2 in H5. auto. apply Prime. }
  apply Lindenbaum_cworld in H2 ; auto. destruct H2 as (v & Hv1 & Hv2).
  assert (cireach  c v). intros C HC ; auto. unfold In in *. unfold th in *. apply Hv1 ; left ; auto.
  assert (cmreach  v w). split.
  { intros. unfold th in *. epose (LEM _). destruct o as [P | NP] ; [exact P | ].
    exfalso. assert ((fun x : form => exists A : form, ~ (let (th, _, _) := w in th) A /\ x = □ A) (□ A)).
    exists A ; split ; auto. apply Hv2 in H4. auto. }
  { intros. unfold th in *. apply Hv1. right ; exists A ; split ; auto. }
    pose (H0 _ H2 _ H3). apply IHψ in f ; auto. assert (~ ((@th w) ψ)).
    apply Hw2. apply In_singleton ; auto.
  auto.
- intros. apply IHψ ; auto. apply H in H0. destruct H1. apply H1 ; auto.
(* Diam ψ *)
- simpl in H0. destruct (LEM (th (◊ ψ))) ; auto. exfalso.
  destruct (H0 _ (cireach_refl c)) as (dc & H2 & H3).
  apply IHψ in H3 ; auto. apply H2 in H3. auto.
- intros. unfold cireach in H. apply H in H0.
  destruct (LEM ((@th v) (◊ ⊥))).
  { exists cexpl. split ; auto. split ; intros ; unfold th in *. unfold cexpl ; cbn ; unfold AllForm ; auto.
    apply Closed. eapply MP. eapply MP. apply Ax ; left ; right ; eapply Kd ; reflexivity. apply Nec. apply EFQ.
    apply Id ; auto. apply IHψ. unfold th ; unfold cexpl ; cbn ; unfold AllForm ; auto. }
  { assert (~ pair_extCKH_prv AdAxCdIdb (Union _ (fun x => exists A, (@th v) (□ A) /\ x = A) (Singleton _ ψ))
        (fun x => exists B, ~ ((@th v) (◊ B)) /\ x = B)).
    { intro. destruct H2 as (l & K0 & K1).
      apply extCKH_Deduction_Theorem in K1. apply K_rule in K1.
      assert (extCKH_prv AdAxCdIdb (Union _ (@th v) (Singleton _ (◊ ψ))) (◊list_disj l)).
      apply extCKH_Detachment_Theorem. eapply MP. apply Ax ; left ; right ; eapply Kd ; reflexivity.
      apply (extCKH_monot _ _ _ K1). intros A HA. destruct HA as (B & K2 & K3) ; subst.
      destruct K2 as (C & K4 & K5) ; subst ; auto. apply extCKH_monot with (Γ1:=@th v) in H2.
      assert (G: extCKH_prv AdAxCdIdb (@th v) (list_disj (map Diam l))).
      { apply more_AdAx_more_prv with (AdAxCd (fun x => AdAx x \/ exists A B, (Idb A B) = x)).
        intros. destruct H3 ; auto. destruct H3. left ; auto. destruct H3. destruct H3 ; subst. right ; eexists ; eexists ; auto.
        destruct H3. destruct H3 ; subst. right ; eexists ; eexists ; auto. apply Diam_distrib_list_disj ; auto.
        intro. subst. cbn in *. unfold th in *. apply H1. apply Closed. auto.
        apply more_AdAx_more_prv with AdAxCdIdb ; auto.
        intros. destruct H3 ; auto. left. auto. destruct H3. destruct H3 ; destruct H3 ; subst.
        right ; eexists ; eexists ; auto. left. right ; eexists ; eexists ; auto. }
      apply Closed in G. apply prime_list_disj in G.
      destruct G. destruct H3. destruct H3 ; subst ; auto. apply in_map_iff in H3. destruct H3.
      destruct H3 ; subst. apply K0 in H5. destruct H5. destruct H3 ; subst ; auto.
      apply H1. apply Closed. eapply MP. apply EFQ. apply Id ; auto. apply Prime.
      intros A HA. inversion HA ; subst ; auto. inversion H3 ; subst ; auto. }
    apply Lindenbaum_cworld in H2. destruct H2 as (w & K0 & K1). exists w. split ; auto.
    split ; intros. apply K0. left ; exists A ; split ; auto.
    destruct (LEM ((@th v) (◊ A))) ; auto. exfalso. assert ((fun x : form => exists B : form, ~ (@th v) (◊ B) /\ x = B) A).
    exists A ; split ; auto. apply K1 in H4. auto.
    apply IHψ. apply K0. right ; apply In_singleton. }
Qed.

(* The canonical frames satisfies the strong Cd condition and weak one of Idb. *)

Lemma CF_strong_Cd_weak_Idb : strong_Cd_weak_Idb_frame CF.
Proof.
split.
- intros x y z ixy mxz.
  destruct (LEM ((@th y) (◊ ⊥))).
  + exists expl. split.
      * split ; intros A HA. unfold th ; unfold cexpl ; cbn ; unfold AllForm ; auto.
        apply Closed. eapply MP. eapply MP. apply Ax ; left ; right ; eapply Kd ; reflexivity. apply Nec.
        apply EFQ. apply Id ; auto.
      * intros A HA ; unfold th ; unfold cexpl ; cbn ; unfold AllForm ; auto.
  + assert (~ pair_extCKH_prv AdAxCdIdb (Union _ (fun B => exists A, (@th y) (□ A) /\ B = A) (@th z))
        (fun B => exists A, ~ ((@th y) (◊ A)) /\ B = A)).
    { intro. destruct H0 as (l & H1 & H2).
      apply partial_finite in H2. destruct H2 as (lz & H3 & H4). apply prv_list_left_conj in H4.
      apply extCKH_Deduction_Theorem in H4. apply K_rule in H4.
      assert (extCKH_prv AdAxCdIdb (@th y) (◊ list_disj l)).
      eapply MP. eapply MP. apply Ax ; left ; right ; eapply Kd ; reflexivity.
      apply (extCKH_monot _ _ _ H4). intros A HA. destruct HA. destruct H0 ; subst.
      destruct H0 ; subst. destruct H0 ; subst ; auto. apply Id. apply ixy.
      apply mxz. apply Closed. apply forall_list_conj. intros ; auto. apply Id ; apply H3 ; auto.
      destruct l. cbn in H0. apply H. apply Closed ; auto.
      assert (G: extCKH_prv AdAxCdIdb (@th y) (list_disj (map Diam (f :: l)))).
      { apply more_AdAx_more_prv with (AdAxCd (fun x => AdAx x \/ exists A B, (Idb A B) = x)).
        intros. destruct H2 ; auto. destruct H2. left ; auto. destruct H2. destruct H2 ; subst. right ; eexists ; eexists ; auto.
        destruct H2. destruct H2 ; subst. right ; eexists ; eexists ; auto. apply Diam_distrib_list_disj ; auto.
        intro. inversion H2. apply more_AdAx_more_prv with AdAxCdIdb ; auto.
        intros. destruct H2 ; auto. left. auto. destruct H2. destruct H2 ; destruct H2 ; subst.
        right ; eexists ; eexists ; auto. left. right ; eexists ; eexists ; auto. }
      apply Closed in G. apply prime_list_disj in G.
      destruct G. destruct H2. destruct H2 ; subst. apply in_map_iff in H2. destruct H2.
      destruct H2 ; subst. apply H1 in H6. destruct H6. destruct H2 ; subst ; auto.
      apply H. apply Closed. eapply MP. apply EFQ. apply Id. auto. apply Prime. }
    apply Lindenbaum_cworld in H0. destruct H0 as (w & H1 & H2). exists w.
    split.
    * split ; intros A HA. apply H1. left. exists A ; auto.
      destruct (LEM ((@th y) (◊ A))) ; auto.
      assert ((fun B : form => exists A : form, ~ (@th y) (◊ A) /\ B = A) A). exists A ; split ; auto.
      apply H2 in H3 ; exfalso ; auto.
    * intros A HA. apply H1. right. auto.
- intros x y z mxy iyz.
  destruct (LEM ((@th z) ⊥)).
  + exists expl. split.
      * intros A HA ; unfold th ; unfold cexpl ; cbn ; unfold AllForm ; auto.
      * split ; intros A HA. 2: unfold th ; unfold cexpl ; cbn ; unfold AllForm ; auto.
        apply Closed. eapply MP. apply EFQ. apply Id ; auto.
  + assert (~ pair_extCKH_prv AdAxCdIdb (Union _ (@th x) (fun B => exists A, (@th z) A /\ B = ◊ A))
        (fun B => exists A, ~ ((@th z) A) /\ B = □ A)).
    { intro. destruct H0 as (l & H1 & H2).
      apply partial_finite in H2. destruct H2 as (lz & H3 & H4). apply prv_list_left_conj in H4.
      destruct (list_Diam_map_repr lz) as (dlz & J0) ; subst. intros. apply H3 in H0. destruct H0. destruct H0 ; subst ; eexists ; auto.
      destruct (list_Box_map_repr l) as (bl & J1) ; subst. intros. apply H1 in H0. destruct H0. destruct H0 ; subst ; eexists ; auto.
      apply list_disj_Box in H4. apply extCKH_Deduction_Theorem in H4.
      assert (extCKH_prv AdAxCdIdb (@th x) (□ (list_conj dlz → list_disj bl))).
      eapply MP. apply Ax ; right ; right ; eexists ; eexists ; right ; reflexivity.
      eapply MP. eapply MP. apply Imp_trans. apply list_conj_Diam_obj. auto.
      apply Closed in H0. apply mxy in H0. apply iyz in H0.
      assert ((@th z) (list_disj bl)).
      apply Closed. eapply MP. apply Id ; exact H0. apply forall_list_conj.
      intros B HB. assert (List.In (◊ B) (map Diam dlz)). apply in_map_iff ; auto. exists B ; split ; auto.
      apply H3 in H2. destruct H2 as (C & HC0 & HC1). inversion HC1 ; subst. unfold th. apply Id ; auto.
      apply prime_list_disj in H2. destruct H2 as (C & HC0 & HC1) ; destruct HC0 ; subst ; auto.
      destruct (H1 (□ C)) as (D & (HD0 & HD1)) ; subst. apply in_map_iff ; exists C ; auto.
      inversion HD1 ; subst. auto. apply Prime. }
    apply Lindenbaum_cworld in H0. destruct H0 as (w & H1 & H2). exists w.
    split.
    * intros A HA. apply H1. left. auto.
    * split ; intros A HA.
      destruct (LEM ((@th z) A)) ; auto.
      assert ((fun B : form => exists A : form, ~ (@th z) A /\ B = □ A) (□ A)). exists A ; split ; auto.
      apply H2 in H3 ; exfalso ; auto.
      apply H1. right. exists A ; auto.
Qed.

(* So, it satisfies both Cd and Idb properties. *)

Lemma CF_CdIdb : Cd_frame CF /\ Idb_frame CF.
Proof.
apply strong_Cd_weak_Idb_Cd_Idb. apply CF_strong_Cd_weak_Idb.
Qed.

(* In fact it satisfies suff_Idb_frame. *)

Lemma CF_suff_Idb : suff_Idb_frame CF.
Proof.
intros x y z mxy iyz.
destruct CF_strong_Cd_weak_Idb. destruct (H0 _ _ _ mxy iyz) as (w & Hw0 & Hw1).
exists w. split ; auto. split ; auto.
intros v Hv. destruct Hv. destruct H1. inversion H1 ; subst.
unfold In. unfold suff_Cd_frame in H. destruct (H _ _ _ H2 Hw1).
destruct H3. exists x1. split ; auto. exists z. split ; auto.
apply In_singleton.
Qed.

(* We leverage the truth lemma to prove a general completeness result parametrised
    in a set of additional axioms validated by a certain class of frames. Completeness
    on this class of frame follows. *)

Variable ClassF : frame -> Prop.
Hypothesis ClassF_AdAx : forall f, ClassF f -> (forall A, AdAxCdIdb A -> fvalid f A).
Hypothesis CF_ClassF : ClassF CF.

Theorem QuasiCompleteness : forall Γ φ,
    ~ extCKH_prv AdAxCdIdb Γ φ -> ~ loc_conseq ClassF Γ φ.
Proof.
intros Γ φ D H.
assert (J: ~ pair_extCKH_prv AdAxCdIdb Γ (Singleton _ φ)).
{ intro. apply D. destruct H0 as (l & H1 & H2). apply forall_list_disj with l ; auto.
  intros. apply H1 in H0. inversion H0 ; subst. apply imp_Id_gen. }
apply Lindenbaum_cworld in J ; auto.
destruct J as (w & H1 & H2).
assert ((forall A, Γ A -> forces CM w A)). intros. apply truth_lemma. apply H1 ; auto.
apply H in H0. apply truth_lemma in H0. pose (H2 φ). apply i ; auto. apply In_singleton.
apply CF_ClassF.
Qed.

Theorem Strong_Completeness : forall Γ φ,
    loc_conseq ClassF Γ φ -> extCKH_prv AdAxCdIdb Γ φ.
Proof.
intros Γ φ LC. pose (QuasiCompleteness Γ φ).
destruct (LEM (extCKH_prv AdAxCdIdb Γ φ)) ; auto. exfalso.
apply n ; assumption.
Qed.

End general_th_completeness.


  
