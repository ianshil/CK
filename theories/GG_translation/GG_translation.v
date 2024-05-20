Require Import Arith.
Require Import Lia.
Require Import Ensembles.
Require Import Init.Wf.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.

Section GG.

(* GG should work here. *)

(* 
(* We could hope that CK validates the GG translation thanks to
    the following. *)

Lemma DNE_Box_Bot Γ : iS4H_prv (Γ, (¬ (¬ (Box Bot))) --> Box Bot).
Proof.
apply Strong_Completeness. intros M x HΓ.
intros y Rxy Hy.
intros u Hu.
exfalso. simpl in *.
apply Hy with y.
- apply reach_refl.
- intros. pose (H0 u Hu).
  pose (Hu v). apply i.
  unfold uset in *. apply i_T ; auto.
Qed.

(* But it does not. To show this, we create an interior
    preorder model with three points A, B and C such
    that A forces ¬ ¬ Box 0, but does not force Box ¬ ¬ 0. *)

(* We first construct the model. *)

Inductive ABC  : Type :=
 | A : ABC
 | B : ABC
 | C : ABC.

Definition ABCreach (n m : ABC) : Prop :=
  match n with
   | A => match m with
                   | A => True
                   | B => True
                   | C => False
                  end
   | B => match m with
                   | A => False
                   | B => True
                   | C => False
                  end
   | C => match m with
                   | A => False
                   | B => False
                   | C => True
                  end
  end.

Lemma ABCreach_refl : forall n, ABCreach n n.
Proof.
intros. destruct n ; unfold ABCreach ; auto.
Qed.

Lemma ABCreach_trans : forall n m k, (ABCreach n m) -> (ABCreach m k) -> (ABCreach n k).
Proof.
intros. unfold ABCreach in * ; destruct n ; auto ; destruct m ; auto ; destruct k ; auto.
Qed.

(* We can create a preord_set of the following form (omitting reflexive arrows): 

                               (A) ==[ABCreach]==> (B)

                                (C)

    So, B can be reached by A, and C is an isolated point. *)

Instance P : preord_set :=
      {|
        nodes := ABC ;
        reachable := ABCreach ;
        reach_refl u := ABCreach_refl u ;
        reach_tran u v w := @ABCreach_trans u v w
      |}.

(* We manually define some upsets in P (the canonical ones). *)

  Lemma ABC_is_upset : forall w, ((Triple _ A B C) w) ->
            forall y, reachable w y -> ((Triple _ A B C) y).
  Proof.
  intros. destruct y ; firstorder.
  Qed.

  Instance ABC_upset : upset P :=
      {|
        uset := Triple _ A B C;
        is_upset := ABC_is_upset
      |}.

  Lemma AB_is_upset : forall w, ((Couple _ A B) w) ->
            forall y, reachable w y -> ((Couple _ A B) y).
  Proof.
  intros. inversion H ; simpl in * ; unfold reachable in H0 ; destruct y ; subst ; firstorder.
  Qed.

  Instance AB_upset : upset P :=
      {|
        uset := Couple _ A B;
        is_upset := AB_is_upset
      |}.

  Lemma BC_is_upset : forall w, ((Couple _ B C) w) ->
            forall y, reachable w y -> ((Couple _ B C) y).
  Proof.
  intros. inversion H ; simpl in * ; unfold reachable in H0 ; destruct y ; subst ; firstorder.
  Qed.

  Instance BC_upset : upset P :=
      {|
        uset := Couple _ B C;
        is_upset := BC_is_upset
      |}.

  Lemma B_is_upset : forall w, ((Singleton _ B) w) ->
            forall y, reachable w y -> ((Singleton _ B) y).
  Proof.
  intros. inversion H ; simpl in * ; unfold reachable in H0 ; destruct y ; subst ; firstorder.
  Qed.

  Instance B_upset : upset P :=
      {|
        uset := Singleton _ B;
        is_upset := B_is_upset
      |}.

  Lemma C_is_upset : forall w, ((Singleton _ C) w) ->
            forall y, reachable w y -> ((Singleton _ C) y).
  Proof.
  intros. inversion H ; simpl in * ; unfold reachable in H0 ; destruct y ; subst ; firstorder.
  Qed.

  Instance C_upset : upset P :=
      {|
        uset := Singleton _ C;
        is_upset := C_is_upset
      |}.

  Lemma Empty_is_upset : forall w, ((Empty_set _) w) ->
            forall y, reachable w y -> ((Empty_set _) y).
  Proof.
  intros. inversion H.
  Qed.

  Instance Empty_upset : upset P :=
      {|
        uset := Empty_set _;
        is_upset := Empty_is_upset
      |}.

(* Then we turn to the definition of our interior operator. *)

Definition i_P : (upset P) -> (upset P).
Proof.
intro. destruct X.
exists (fun x =>
  ((uset A /\ uset B /\ uset C)) \/ (* For {A,B,C} *)
  (uset A /\ uset B /\ (~ (uset C)) /\ x = B) \/ (* For {A,B} *)
  (~ (uset A) /\ uset B /\ ~ (uset C) /\ x = B) \/ (* For {B} *)
  ((~ (uset A)) /\ (~ (uset B)) /\ uset C /\ x = C) \/ (* For {C} *)
  ((~ (uset A)) /\ uset B /\ uset C /\ (x = B \/ x = C)) (* For {B,C} *)
).
intros D H0. destruct H0 as [H0 | [H0 | [H0 | [H0 | H0]]]] ;
intros E reachDE.
destruct H0 as (H1 & H2 & H3) ; auto.
all: destruct H0 as (H1 & H2 & H3 & H4) ; unfold reachable in reachDE ; subst.
- right ; left ; repeat split ; auto. destruct E ; auto ; subst ; try contradiction.
- right ; right ; left ; repeat split ; auto. destruct E ; auto ; subst ; try contradiction.
- right ; right ; right ; left ; repeat split ; auto. destruct E ; auto ; subst ; try contradiction.
- right ; right ; right ; right ; repeat split ; auto. destruct H4 ; subst ; auto ; destruct E ; auto ; subst ; try contradiction.
Defined.

(* The next lemma shows that upset in our preord_set have a canonical representation. Note that in the
    proof of it, we use LEM: as Ensembles are functions to Prop in Coq, and thus our upsets are defined over
    these functions, to prove that two functions are equal we can assume LEM. We could get rid of this feature
    by requiring that our semantics accepts only upsets which are decidable. *)

Lemma canonical_form_upset_P : forall (u : upset P), (@uset _ u = Triple _ A B C) \/
                                                                                      (@uset _ u = Couple _ A B) \/
                                                                                      (@uset _ u = Couple _ B C) \/
                                                                                      (@uset _ u = Singleton _ B) \/
                                                                                      (@uset _ u = Singleton _ C) \/
                                                                                      (@uset _ u = Empty_set _).
Proof.
intros. destruct u. simpl in *.
destruct (LEM (uset A)).
- destruct (LEM (uset C)).
  + left. apply Extensionality_Ensembles. split ; intros D HD ; auto.
     destruct D ; firstorder. inversion HD ; firstorder.
  + right. left. apply Extensionality_Ensembles. split ; intros D HD ; auto.
     destruct D ; firstorder. inversion HD ; firstorder.
- destruct (LEM (uset B)).
  + destruct (LEM (uset C)).
    * right. right. left. apply Extensionality_Ensembles. split ; intros D HD ; auto.
      destruct D ; firstorder. inversion HD ; firstorder.
    * right. right. right. left. apply Extensionality_Ensembles. split ; intros D HD ; auto.
      destruct D ; firstorder. inversion HD ; firstorder.
  + destruct (LEM (uset C)).
    * right. right. right. right. left. apply Extensionality_Ensembles. split ; intros D HD ; auto.
      destruct D ; firstorder. inversion HD ; firstorder.
    * right. right. right. right. right. apply Extensionality_Ensembles. split ; intros D HD ; auto.
      destruct D ; firstorder. inversion HD ; firstorder.
Qed.

Lemma i_ABC : forall (u : upset P), (@uset _ u = Triple _ A B C) -> (@uset _ (i_P u) = Triple _ A B C).
Proof.
intros. unfold uset in *. destruct u ; simpl in *.
apply Extensionality_Ensembles. split ; intros D HD ; auto.
- destruct D ; firstorder.
- unfold In in *. left. rewrite H ; firstorder.
Qed.

Lemma i_AB : forall (u : upset P), (@uset _ u = Couple _ A B) -> (@uset _ (i_P u) = Singleton _ B).
Proof.
intros. unfold uset in *. destruct u ; simpl in *.
apply Extensionality_Ensembles. split ; intros D HD ; auto ; unfold In in *.
- subst. destruct HD as [H0 | [H0 | [H0 | [H0 | H0]]]] ; subst ; firstorder.
  1,4,6: inversion H1.
  1-3: rewrite H2 ; apply In_singleton.
- inversion HD ; subst. right. left ; firstorder. intro. inversion H.
Qed.

Lemma i_BC : forall (u : upset P), (@uset _ u = Couple _ B C) -> (@uset _ (i_P u) = Couple _ B C).
Proof.
intros. unfold uset in *. destruct u ; simpl in *.
apply Extensionality_Ensembles. split ; intros D HD ; auto ; unfold In in *.
- subst. destruct HD as [H0 | [H0 | [H0 | [H0 | H0]]]] ; subst ; firstorder.
  1-2: inversion H.
  1-4: rewrite H2 ; firstorder.
- right. right. subst. right. right. inversion HD ; subst ; firstorder. 1-2: intro ; inversion H.
Qed.

Lemma i_B : forall (u : upset P), (@uset _ u = Singleton _ B) -> (@uset _ (i_P u) = Singleton _ B).
Proof.
intros. unfold uset in *. destruct u ; simpl in *.
apply Extensionality_Ensembles. split ; intros D HD ; auto ; unfold In in *.
- subst. destruct HD as [H0 | [H0 | [H0 | [H0 | H0]]]] ; subst ; firstorder.
  1-2: inversion H.
  1-3: rewrite H2 ; firstorder.
- right. right. subst. left. inversion HD ; subst ; firstorder. 1-2: intro ; inversion H.
Qed.

Lemma i_C : forall (u : upset P), (@uset _ u = Singleton _ C) -> (@uset _ (i_P u) = Singleton _ C).
Proof.
intros. unfold uset in *. destruct u ; simpl in *.
apply Extensionality_Ensembles. split ; intros D HD ; auto ; unfold In in *.
- subst. destruct HD as [H0 | [H0 | [H0 | [H0 | H0]]]] ; subst ; firstorder.
  1: inversion H.
  1-3: rewrite H2 ; firstorder.
- right. right. subst. right ; left. inversion HD ; subst ; firstorder. 1-2: intro ; inversion H.
Qed.

Lemma i_Empty : forall (u : upset P), (@uset _ u = Empty_set _) -> (@uset _ (i_P u) = Empty_set _).
Proof.
intros. unfold uset in *. destruct u ; simpl in *.
apply Extensionality_Ensembles. split ; intros D HD ; auto.
- destruct HD as [H0 | [H0 | [H0 | [H0 | H0]]]] ; subst ; firstorder.
- inversion HD.
Qed.

Lemma i_P_unit : i_P (unit_upset P) = (unit_upset P).
Proof.
apply upset_prf_irrel. rewrite i_ABC ; unfold uset ; unfold nodes in *.
all: unfold unit_upset ; apply Extensionality_Ensembles ; split ; intros D HD ; 
destruct D ; subst ; firstorder.
Qed.

Lemma i_P_inter : forall u0 u1, @uset _ (i_P (inter_upset P u0 u1)) = @uset _ (inter_upset P (i_P u0) (i_P u1)).
Proof.
intros u0 u1. unfold uset in *.
destruct (canonical_form_upset_P u0) as [Hu0 | [Hu0 | [Hu0 | [Hu0 | [Hu0 | Hu0]]]]].
- unfold uset in *. pose (i_ABC _ Hu0). unfold uset in *.
  destruct (canonical_form_upset_P u1) as [Hu1 | [Hu1 | [Hu1 | [Hu1 | [Hu1 | Hu1]]]]] ; unfold uset in *.
  + pose (i_ABC _ Hu1). unfold uset in *. apply Extensionality_Ensembles. split ; intros D HD ; unfold In in *.
     1-2: simpl in * ; unfold uset in * ; subst ; destruct u0 ; destruct u1 ; subst ; firstorder.
  + pose (i_AB _ Hu1). unfold uset in *. apply Extensionality_Ensembles. split ; intros D HD ; unfold In in *.
     1-2: simpl in * ; unfold uset in * ; subst ; destruct u0 ; destruct u1 ; subst ; firstorder.
     1-2: rewrite H2 in * ; simpl ; right ; left ; firstorder ; intro G ; inversion G.
  + pose (i_BC _ Hu1). unfold uset in *. apply Extensionality_Ensembles. split ; intros D HD ; unfold In in *.
     1-2: simpl in * ; unfold uset in * ; subst ; destruct u0 ; destruct u1 ; subst ; firstorder.
     1-4: rewrite H2 in * ; simpl ; right ; right ; right ; right ; firstorder ; intro G ; inversion G.
  + pose (i_B _ Hu1). unfold uset in *. apply Extensionality_Ensembles. split ; intros D HD ; unfold In in *.
     1-2: simpl in * ; unfold uset in * ; subst ; destruct u0 ; destruct u1 ; subst ; firstorder.
     1-2,4: rewrite H2 in * ; simpl ; right ; right ; left ; firstorder ; intro G ; inversion G.
     1-2: inversion H3.
  + pose (i_C _ Hu1). unfold uset in *. apply Extensionality_Ensembles. split ; intros D HD ; unfold In in *.
     1-2: simpl in * ; unfold uset in * ; subst ; destruct u0 ; destruct u1 ; subst ; firstorder. inversion H3.
     1,3: rewrite H2 in * ; simpl ; right ; right ; right ; left ; firstorder ; intro G ; inversion G. inversion H4.
  + pose (i_Empty _ Hu1). unfold uset in *. apply Extensionality_Ensembles. split ; intros D HD ; unfold In in *.
     1-2: simpl in * ; unfold uset in * ; subst ; destruct u0 ; destruct u1 ; subst ; simpl ; firstorder.
- unfold uset in *. pose (i_AB _ Hu0). unfold uset in *.
  destruct (canonical_form_upset_P u1) as [Hu1 | [Hu1 | [Hu1 | [Hu1 | [Hu1 | Hu1]]]]] ; unfold uset in *.
  + pose (i_ABC _ Hu1). unfold uset in *. apply Extensionality_Ensembles. split ; intros D HD ; unfold In in *.
     1-2: simpl in * ; unfold uset in * ; subst ; destruct u0 ; destruct u1 ; subst ; firstorder.
     1-2: rewrite H2 in * ; simpl ; right ; left ; firstorder ; intro G ; inversion G.
  + pose (i_AB _ Hu1). unfold uset in *. apply Extensionality_Ensembles. split ; intros D HD ; unfold In in *.
     1-2: simpl in * ; unfold uset in * ; subst ; destruct u0 ; destruct u1 ; subst ; firstorder.
  + pose (i_BC _ Hu1). unfold uset in *. apply Extensionality_Ensembles. split ; intros D HD ; unfold In in *.
     1-2: simpl in * ; unfold uset in * ; subst ; destruct u0 ; destruct u1 ; subst ; firstorder. inversion H4. 3-5: inversion H1.
     rewrite H2 in * ; simpl ; right ; left ; firstorder ; intro G ; inversion G.
     rewrite H2 in * ; simpl ; right ; right ; right ; right ; firstorder ; intro G ; inversion G.
  + pose (i_B _ Hu1). unfold uset in *. apply Extensionality_Ensembles. split ; intros D HD ; unfold In in *.
     1-2: simpl in * ; unfold uset in * ; subst ; destruct u0 ; destruct u1 ; subst ; firstorder. inversion H4.
     1-2: rewrite H2 in * ; simpl ; right ; left ; firstorder ; intro G ; inversion G.
     rewrite H2 in * ; simpl ; right ; right ; left ; firstorder ; intro G ; inversion G.
     1-3: inversion H3.
  + pose (i_C _ Hu1). unfold uset in *. apply Extensionality_Ensembles. split ; intros D HD ; unfold In in *.
     1-2: simpl in * ; unfold uset in * ; subst ; destruct u0 ; destruct u1 ; subst ; firstorder. inversion H3. 1-3: inversion H1.
     1-2: rewrite H3 in H6 ; inversion H6.
  + pose (i_Empty _ Hu1). unfold uset in *. apply Extensionality_Ensembles. split ; intros D HD ; unfold In in *.
     1-2: simpl in * ; unfold uset in * ; subst ; destruct u0 ; destruct u1 ; subst ; simpl ; firstorder.
- unfold uset in *. pose (i_BC _ Hu0). unfold uset in *.
  destruct (canonical_form_upset_P u1) as [Hu1 | [Hu1 | [Hu1 | [Hu1 | [Hu1 | Hu1]]]]] ; unfold uset in *.
  + pose (i_ABC _ Hu1). unfold uset in *. apply Extensionality_Ensembles. split ; intros D HD ; unfold In in *.
     1-2: simpl in * ; unfold uset in * ; subst ; destruct u0 ; destruct u1 ; subst ; firstorder.
     1-4: rewrite H2 in * ; simpl ; right ; right ; right ; right ; firstorder ; intro G ; inversion G.
  + pose (i_AB _ Hu1). unfold uset in *. apply Extensionality_Ensembles. split ; intros D HD ; unfold In in *.
     1-2: simpl in * ; unfold uset in * ; subst ; destruct u0 ; destruct u1 ; subst ; firstorder. 4: inversion H3.
     1-3: rewrite H2 in * ; simpl ; right ; right ; right ; right ; firstorder ; intro G ; inversion G. inversion H.
     rewrite H2 in * ; simpl ; right ; left ; firstorder ; intro G ; inversion G.
  + pose (i_BC _ Hu1). unfold uset in *. apply Extensionality_Ensembles. split ; intros D HD ; unfold In in *.
     1-2: simpl in * ; unfold uset in * ; subst ; destruct u0 ; destruct u1 ; subst ; firstorder.
  + pose (i_B _ Hu1). unfold uset in *. apply Extensionality_Ensembles. split ; intros D HD ; unfold In in *.
     1-2: simpl in * ; unfold uset in * ; subst ; destruct u0 ; destruct u1 ; subst ; firstorder.
     1-4: rewrite H2 in * ; simpl ; right ; right ; right ; right ; firstorder ; intro G ; inversion G.
     1-2: rewrite H2 in * ; simpl ; right ; right ; left ; firstorder ; intro G ; inversion G.
     1-3: inversion H3.
  + pose (i_C _ Hu1). unfold uset in *. apply Extensionality_Ensembles. split ; intros D HD ; unfold In in *.
     1-2: simpl in * ; unfold uset in * ; subst ; destruct u0 ; destruct u1 ; subst ; firstorder. inversion H3.
     1-4: rewrite H2 in * ; simpl ; right ; right ; right ; right ; firstorder ; intro G ; inversion G.
     1: rewrite H2 in * ; simpl ; right ; right ; right ; left ; firstorder ; intro G ; inversion G.
     1-2: inversion H4.
  + pose (i_Empty _ Hu1). unfold uset in *. apply Extensionality_Ensembles. split ; intros D HD ; unfold In in *.
     1-2: simpl in * ; unfold uset in * ; subst ; destruct u0 ; destruct u1 ; subst ; simpl ; firstorder.
- unfold uset in *. pose (i_B _ Hu0). unfold uset in *.
  destruct (canonical_form_upset_P u1) as [Hu1 | [Hu1 | [Hu1 | [Hu1 | [Hu1 | Hu1]]]]] ; unfold uset in *.
  + pose (i_ABC _ Hu1). unfold uset in *. apply Extensionality_Ensembles. split ; intros D HD ; unfold In in *.
     1-2: simpl in * ; unfold uset in * ; subst ; destruct u0 ; destruct u1 ; subst ; firstorder. inversion H.
     1,3: rewrite H2 in * ; simpl ; right ; right ; left ; firstorder ; intro G ; inversion G. all: inversion H1.
  + pose (i_AB _ Hu1). unfold uset in *. apply Extensionality_Ensembles. split ; intros D HD ; unfold In in *.
     1-2: simpl in * ; unfold uset in * ; subst ; destruct u0 ; destruct u1 ; subst ; firstorder. 4: inversion H3. inversion H.
     rewrite H2 in * ; simpl ; right ; right ; left ; firstorder ; intro G ; inversion G. 1-2: inversion H1. inversion H.
     rewrite H2 in * ; simpl ; right ; left ; firstorder ; intro G ; inversion G.
  + pose (i_BC _ Hu1). unfold uset in *. apply Extensionality_Ensembles. split ; intros D HD ; unfold In in *.
     1-2: simpl in * ; unfold uset in * ; subst ; destruct u0 ; destruct u1 ; subst ; firstorder.
     1-2,4: rewrite H2 in * ; simpl ; right ; right ; left ; firstorder ; intro G ; inversion G. 1-2: inversion H1.
     1-2: rewrite H2 in * ; simpl ; right ; right ; right ; right ; firstorder ; intro G ; inversion G. all: inversion H1.
  + pose (i_B _ Hu1). unfold uset in *. apply Extensionality_Ensembles. split ; intros D HD ; unfold In in *.
     1-2: simpl in * ; unfold uset in * ; subst ; destruct u0 ; destruct u1 ; subst ; firstorder.
  + pose (i_C _ Hu1). unfold uset in *. apply Extensionality_Ensembles. split ; intros D HD ; unfold In in *.
     1-2: simpl in * ; unfold uset in * ; subst ; destruct u0 ; destruct u1 ; subst ; firstorder. inversion H3. inversion H1.
     1-2: inversion H4. inversion H3. inversion H1. inversion H4. inversion H4. inversion H. rewrite H3 in H6 ; inversion H6.
  + pose (i_Empty _ Hu1). unfold uset in *. apply Extensionality_Ensembles. split ; intros D HD ; unfold In in *.
     1-2: simpl in * ; unfold uset in * ; subst ; destruct u0 ; destruct u1 ; subst ; simpl ; firstorder.
- unfold uset in *. pose (i_C _ Hu0). unfold uset in *.
  destruct (canonical_form_upset_P u1) as [Hu1 | [Hu1 | [Hu1 | [Hu1 | [Hu1 | Hu1]]]]] ; unfold uset in *.
  + pose (i_ABC _ Hu1). unfold uset in *. apply Extensionality_Ensembles. split ; intros D HD ; unfold In in *.
     1-2: simpl in * ; unfold uset in * ; subst ; destruct u0 ; destruct u1 ; subst ; firstorder. inversion H0.
     1,3: rewrite H2 in * ; simpl ; right ; right ; right ; left ; firstorder ; intro G ; inversion G. inversion H0.
  + pose (i_AB _ Hu1). unfold uset in *. apply Extensionality_Ensembles. split ; intros D HD ; unfold In in *.
     1-2: simpl in * ; unfold uset in * ; subst ; destruct u0 ; destruct u1 ; subst ; firstorder. 4: inversion H3. inversion H0. 1-2: inversion H3.
     1-2: rewrite H3 in H6 ; inversion H6.
  + pose (i_BC _ Hu1). unfold uset in *. apply Extensionality_Ensembles. split ; intros D HD ; unfold In in *.
     1-2: simpl in * ; unfold uset in * ; subst ; destruct u0 ; destruct u1 ; subst ; firstorder. inversion H0.
     1,3: rewrite H2 in * ; simpl ; right ; right ; right ; left ; firstorder ; intro G ; inversion G. 1-2: inversion H0.
     1-2: rewrite H2 in * ; simpl ; right ; right ; right ; right ; firstorder ; intro G ; inversion G. all: inversion H0.
  + pose (i_B _ Hu1). unfold uset in *. apply Extensionality_Ensembles. split ; intros D HD ; unfold In in *.
     1-2: simpl in * ; unfold uset in * ; subst ; destruct u0 ; destruct u1 ; subst ; firstorder. 1,3-5,7-8: inversion H0. 1-2:inversion H3.
     1-2: rewrite H3 in H6 ; inversion H6.
  + pose (i_C _ Hu1). unfold uset in *. apply Extensionality_Ensembles. split ; intros D HD ; unfold In in *.
     1-2: simpl in * ; unfold uset in * ; subst ; destruct u0 ; destruct u1 ; subst ; firstorder.
  + pose (i_Empty _ Hu1). unfold uset in *. apply Extensionality_Ensembles. split ; intros D HD ; unfold In in *.
     1-2: simpl in * ; unfold uset in * ; subst ; destruct u0 ; destruct u1 ; subst ; simpl ; firstorder.
-  unfold uset in *. apply Extensionality_Ensembles. split ; intros D HD ; unfold In in *.
   1-2: simpl in * ; unfold uset in * ; subst ; destruct u0 ; destruct u1 ; subst ; simpl ; firstorder.
Qed.

Lemma i_P_T : forall u, Included _ (@uset P (i_P u)) (@uset P u).
Proof.
intros. unfold uset. intros D HD. unfold In in *.
destruct (canonical_form_upset_P u) as [Hu | [Hu | [Hu | [Hu | [Hu | Hu]]]]] ; unfold uset in * ; rewrite Hu in *.
- destruct D ; firstorder.
- pose (i_AB _ Hu). unfold uset in * ; rewrite e in *. inversion HD ; firstorder.
- pose (i_BC _ Hu). unfold uset in * ; rewrite e in *. inversion HD ; firstorder.
- pose (i_B _ Hu). unfold uset in * ; rewrite e in *. inversion HD ; firstorder.
- pose (i_C _ Hu). unfold uset in * ; rewrite e in *. inversion HD ; firstorder.
- pose (i_Empty _ Hu). unfold uset in * ; rewrite e in *. inversion HD ; firstorder.
Qed.

Lemma i_P_4 : forall u, Included _ (@uset P (i_P u)) (@uset P (i_P (i_P u))).
Proof.
intros. unfold uset. intros D HD. unfold In in *.
destruct (canonical_form_upset_P u) as [Hu | [Hu | [Hu | [Hu | [Hu | Hu]]]]] ; unfold uset in *.
- pose (i_ABC _ Hu). unfold uset in * ; rewrite e in *.
  pose (i_ABC _ e). unfold uset in * ; rewrite e0 in *. inversion HD ; firstorder.
- pose (i_AB _ Hu). unfold uset in * ; rewrite e in *.
  pose (i_B _ e). unfold uset in * ; rewrite e0 in *. inversion HD ; firstorder.
- pose (i_BC _ Hu). unfold uset in * ; rewrite e in *.
  pose (i_BC _ e). unfold uset in * ; rewrite e0 in *. inversion HD ; firstorder.
- pose (i_B _ Hu). unfold uset in * ; rewrite e in *.
  pose (i_B _ e). unfold uset in * ; rewrite e0 in *. inversion HD ; firstorder.
- pose (i_C _ Hu). unfold uset in * ; rewrite e in *.
  pose (i_C _ e). unfold uset in * ; rewrite e0 in *. inversion HD ; firstorder.
- pose (i_Empty _ Hu). unfold uset in * ; rewrite e in *.
  pose (i_Empty _ e). unfold uset in * ; rewrite e0 in *. inversion HD ; firstorder.
Qed.

Definition val_P : nat -> (upset P) :=
fun n => match n with
| 0 => B_upset
| S n => Empty_upset
end.

(* We finally can define our model. *)

Instance M : model :=
      {|
        pre := P ;

        i := i_P ;
        i_unit := i_P_unit ;
        i_inter := i_P_inter ;
        i_T := i_P_T ;
        i_4 := i_P_4 ;

        val := val_P ;
      |}.

(* We show that our model is indeed a countermodel
    to the formula mentioned initially. *)

Lemma Failure : (iS4H_prv (Empty_set _, (¬ (¬ (Box (# 0)))) --> Box (¬ (¬ (# 0))))) -> False.
Proof.
intro. apply Soundness in H. simpl in H.
epose (H M A).
assert (H0: forall ψ : form, In form (Empty_set form) ψ -> forces M A ψ).
intros psi Hpsi ; inversion Hpsi.

(* A forces the antecendent. *)
assert (H1: forces M A ((¬ (¬ Box # 0)))).
intros D reachAD HD. unfold reachable in reachAD. simpl in reachAD.
destruct D ; auto ; simpl.
1-2: apply HD with B ; auto ; intros ; unfold uset in * ; simpl in H1.
1-2: assert (J: (let (uset, _) := u in uset) = Singleton ABC B).
1,3: apply Extensionality_Ensembles ; split ; intros E HE ; firstorder.
1-2: pose (i_B u J) ; unfold uset in e ; unfold i ; simpl ; rewrite <- e in H1.
1-2: apply H1 ; destruct u ; rewrite J ; firstorder.

(* But A forcing the consequent leads to a contradiction. *)
assert (F: forces M A (Box (¬ (¬ # 0)))).
pose (f H0 A (reach_refl A)). simpl in f0. simpl. intros.
apply f0 ; auto.
epose (force_Box_interior_truthset _ M A). destruct i.
clear H3. pose (H2 F). unfold uset in u.
assert ((let (uset, _) := (truthset_upset M (¬ (¬ # 0))) in uset) = Couple _ A B).
{ simpl. apply Extensionality_Ensembles. split ; intros D HD ; unfold In in *.
  - destruct D. 1-2: firstorder. exfalso. apply HD with C. apply I. intros. destruct v ; auto.
    inversion H4.
  - inversion HD ; subst. intros. destruct v ; auto. 1-2: apply H4 with B ; auto ; apply In_singleton.
    intros. destruct v ; auto. apply H4 with B ; auto ; apply In_singleton. }
apply i_AB in H3. unfold uset in H3.
unfold i in u. destruct (truthset_upset M (¬ (¬ # 0))). simpl in u. simpl in H3.
assert (Singleton ABC B A). rewrite <- H3.
destruct u as [(u0 & u1 & u2) | [(u0 & u1 & u2 & u3) | [(u0 & u1 & u2 & u3) | [(u0 & u1 & u2 & u3) | (u0 & u1 & u2 & u3)]]]] ; subst ; auto.
1-4: inversion u3 ; inversion H4. inversion H4.
Qed. *)

End GG.