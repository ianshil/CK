Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_sem.


Axiom LEM : forall P, P \/ ~ P.

Section Cd.


Definition mupcone (F : frame) (a : nodes -> Prop) := fun w => exists v, a v /\ mreachable v w.
Definition mdowncone (F : frame) (a : nodes -> Prop) := fun w => exists v, a v /\ mreachable w v.
Definition iupcone (F : frame) (a : nodes -> Prop) := fun w => exists v, a v /\ ireachable v w.
Definition idowncone (F : frame) (a : nodes -> Prop) := fun w => exists v, a v /\ ireachable w v.

(* A sufficient condition to prove the axiom Cd (⬦φ ∨ ψ)-->  (⬦φ) ∨ (⬦ψ) is given below. *)

Definition suff_Cd_frame (F : frame) := forall x, exists x', ireachable x x' /\
        forall y z, ireachable x y -> mreachable x' z -> exists w, mreachable y w /\ ireachable z w.

Lemma sufficient_Cd : forall F,
                  suff_Cd_frame F -> forall φ ψ, fvalid F (Cd φ ψ).
Proof.
intros F H φ ψ M frameEq w v iwv Hv ; subst ; cbn in *.
destruct (H v) as (x & Hx0 & Hx1).
destruct (Hv _ Hx0) as (u & Hu0 & Hu1) ; subst ; auto.
destruct Hu1.
- left. intros. destruct (Hx1 _ _ H1 Hu0) as (y & Hy0 & Hy1). exists y ; split;  auto. apply Persistence with u ; auto.
- right. intros. destruct (Hx1 _ _ H1 Hu0) as (y & Hy0 & Hy1). exists y ; split;  auto. apply Persistence with u ; auto.
Qed.

Definition strong_Cd_frame (F : frame) := forall w v u, ireachable w v -> mreachable w u -> exists x, mreachable v x /\ ireachable u x.

Lemma strong_is_suff_Cd : forall F,
                  strong_Cd_frame F -> suff_Cd_frame F.
Proof.
intros F HF x. exists x ; repeat split.
- apply ireach_refl.
- intros. destruct (HF _ _ _ H H0). exists x0 ; firstorder.
Qed.

(* The axiom Cd corresponds to the following frame property. *)

Definition Cd_frame (F : frame) := forall x y z, ireachable x y -> ireachable x z ->
                                     ~ (mdowncone F (Singleton _ expl) y) -> ~ (mdowncone F (Singleton _ expl) z) ->
                    exists w, ireachable x w /\
                                  Included _ (mupcone F (Singleton _ w)) (idowncone F (mupcone F (Singleton _ y))) /\
                                  Included _ (mupcone F (Singleton _ w)) (idowncone F (mupcone F (Singleton _ z))).

Lemma correspond_Cd: forall F,
                  Cd_frame F <-> forall φ ψ, fvalid F (Cd φ ψ).
Proof.
intros F ; split ; intro H.
- intros φ ψ M frameEq w v iwv Hv ; subst.
  epose (LEM _). destruct o as [P | NP] ; [exact P | exfalso ].
  assert (exists y, ireachable v y /\ forall s, mreachable y s -> ~ forces M s φ).
  { epose (LEM _). destruct o as [P0 | NP0] ; [exact P0 | exfalso ].
    apply NP. left. intros u ivu. epose (LEM _). destruct o as [P1 | NP1] ; [exact P1 | exfalso ].
    apply NP0. exists u. split ; auto. intros. intro. apply NP1. exists s ; split ; auto. }
  destruct H0 as (y &Hy0 & Hy1).
  assert (exists z, ireachable v z /\ forall s, mreachable z s -> ~ forces M s ψ).
  { epose (LEM _). destruct o as [P0 | NP0] ; [exact P0 | exfalso ].
    apply NP. right. intros u ivu. epose (LEM _). destruct o as [P1 | NP1] ; [exact P1 | exfalso ].
    apply NP0. exists u. split ; auto. intros. intro. apply NP1. exists s ; split ; auto. }
  destruct H0 as (z &Hz0 & Hz1).
  destruct (H _ _ _ Hy0 Hz0) as (w0 & J0 & J1 & J2).
  1-2: intros K ; destruct K as (u & Hu0 & Hu1) ; inversion Hu0 ; subst.
  apply Hy1 with expl ; auto. apply Expl.
  apply Hz1 with expl ; auto. apply Expl.
  destruct (Hv _ J0) as (u & Hu0 & [Hu1 | Hu1]) ; cbn in Hu1.
  assert ((idowncone fra (mupcone fra (Singleton nodes y))) u).
  apply J1. exists w0 ; split ; auto. apply In_singleton.
  destruct H0 as (t & K0 & K1). destruct K0 as (s & K2 & K3).
  inversion K2 ; subst. apply Hy1 with t ; auto. apply Persistence with u ; auto.
  assert ((idowncone fra (mupcone fra (Singleton nodes z))) u).
  apply J2. exists w0 ; split ; auto. apply In_singleton.
  destruct H0 as (t & K0 & K1). destruct K0 as (s & K2 & K3).
  inversion K2 ; subst. apply Hz1 with t ; auto. apply Persistence with u ; auto.
- intros x y z H0 H1 R0 R1.
  epose (LEM _). destruct o as [P | NP] ; [exact P | exfalso ].
  remember (fun (v : nodes) (p : nat) => (~ (idowncone F (mupcone F (Singleton _ y)) v) /\ p = 0) \/
                                                               (~ (idowncone F (mupcone F (Singleton _ z)) v) /\ p = 1) \/ v = expl) as Val.
  assert (J0: forall u v : nodes, ireachable u v -> forall p : nat, Val u p -> Val v p).
  { intros. subst. destruct H3 as [(H3 & H4) | [(H3 & H4) | H3]] ; subst.
    + left. split ; auto. intro. apply H3. destruct H4 as (x0 & (x1 & L0 & L1) & K1).
       inversion L0 ; subst. exists x0. split ; auto. exists x1 ; split ; auto. apply ireach_tran with v ; auto.
    + right ; left. split ; auto. intro. apply H3. destruct H4 as (x0 & (x1 & L0 & L1) & K1).
       inversion L0 ; subst. exists x0. split ; auto. exists x1 ; split ; auto. apply ireach_tran with v ; auto.
    + right ; right. apply ireach_expl in H2 ; auto. }
  assert (J1: forall p : nat, Val expl p).
  { intro p. subst. right ; right ; auto. }
  pose (Build_model F Val J0 J1).
  assert (~ forces m x ((⬦ (#0)) ∨ (⬦ (#1)))).
  { intro. cbn in H2. destruct H2.
    + destruct (H2 _ H0) as (x0 & K0 & K1). rewrite HeqVal in K1. destruct K1 as [(K1 & K2) | [(K1 & K2) | k1]] ; try lia.
       - apply K1. exists x0. split. exists y ; split ; auto. apply In_singleton. apply ireach_refl.
       - subst. apply R0. exists expl. split ; auto. apply In_singleton.
    + destruct (H2 _ H1) as (x0 & K0 & K1). rewrite HeqVal in K1. destruct K1 as [(K1 & K2) | [(K1 & K2) | k1]] ; try lia.
       - apply K1. exists x0. split. exists z ; split ; auto. apply In_singleton. apply ireach_refl.
       - subst. apply R1. exists expl. split ; auto. apply In_singleton. }
  assert (forces m x (⬦ ((#0) ∨ (#1)))).
  { intros v ixv. epose (LEM _). destruct o as [P0 | NP0] ; [exact P0 | exfalso ].
    apply NP. exists v. repeat split ; auto. 1-2: intros s Hs.
    epose (LEM _). destruct o as [P1 | NP1] ; [exact P1 | exfalso ].
    apply NP0. exists s. split. destruct Hs as (k & HK0 & HK1) ; inversion HK0 ; subst ; auto.
    left. cbn. subst. left ; split ; auto.
    epose (LEM _). destruct o as [P1 | NP1] ; [exact P1 | exfalso ].
    apply NP0. exists s. split. destruct Hs as (k & HK0 & HK1) ; inversion HK0 ; subst ; auto.
    right. cbn. subst. right ; left ; split ; auto. }
   apply H2. cbn. pose (H (# 0) (# 1) m (eq_refl) x). apply f. apply ireach_refl.
    apply H3.
Qed.

Lemma suff_impl_Cd  : forall F, suff_Cd_frame F -> Cd_frame F.
Proof.
intros F H x y z ixy ixz Hy Hz.
destruct (H x) as (w & Hw0 & Hw1). exists w. repeat split ; auto.
- intros v Hv. destruct Hv as (u & Hu0 & Hu1). inversion Hu0 ; subst.
  destruct (Hw1 _ _ ixy Hu1) as (r & Hr0 & Hr1). exists r ; split ; auto.
  exists y ; auto. repeat split ; auto.
- intros v Hv. destruct Hv as (u & Hu0 & Hu1). inversion Hu0 ; subst.
  destruct (Hw1 _ _ ixz Hu1) as (r & Hr0 & Hr1). exists r ; split ; auto.
  exists z ; auto. repeat split ; auto.
Qed.

End Cd.







Section Idb.

Definition suff_Idb_frame (F : frame) := forall x y z, mreachable x y -> ireachable y z ->
                    exists u, ireachable x u /\
                                  Included _ (iupcone F (Singleton _ u)) (mdowncone F (iupcone F (Singleton _ z))) /\
                                  mreachable u z.

Lemma sufficient_Idb : forall F,
                  suff_Idb_frame F -> forall φ ψ, fvalid F (Idb φ ψ).
Proof.
intros F H φ ψ M frameEq x y ixy Hy ; subst.
- epose (LEM _). destruct o as [P | NP] ; [exact P | exfalso ].
  assert (exists u v w, ireachable y u /\ mreachable u v /\ ireachable v w /\ forces M w φ /\ ~ forces M w ψ).
  { epose (LEM _). destruct o as [P0 | NP0] ; [exact P0 | ].
    exfalso. apply NP. intros u ivu r mur s irs Hs ; subst. epose (LEM _). destruct o as [P1 | NP1] ; [exact P1 | ].
    exfalso. apply NP0. exists u,r,s. repeat split ; auto. }
  destruct H0 as (u & v & w & iyu & muv & ivw & Hw & NHw).
  destruct (H _ _ _ muv ivw) as (u0 & iuu0 & cones & mu0w).
  assert (forces M u0 (⬦ φ)).
  { intros v1 iu0v1.
    assert ((iupcone fra (Singleton nodes u0)) v1). exists u0. split ; auto.
    apply In_singleton.
    apply cones in H0. destruct H0. destruct H0. destruct H0. destruct H0. inversion H0 ; subst.
    exists x0. split ; auto. apply Persistence with x1 ; auto. }
  assert (~ forces M u0 (☐ ψ)).
  { intro ctr. pose (ctr _ (ireach_refl u0) _ mu0w). apply NHw. apply Persistence with w ; auto.
    apply ireach_refl. }
  apply H1. intros v1 iu0v1 u1 mv1u1. cbn in Hy. apply Hy with u0 v1 ; auto.
  apply ireach_tran with u ; auto.
Qed.

(* The axiom Idb ((⬦φ) --> (☐ψ)) -->  ☐(φ --> ψ) corresponds to the following frame property. *)

Definition Idb_frame (F : frame) := forall x y z, mreachable x y -> ireachable y z -> z <> expl ->
                    exists u v w, ireachable x u /\
                                  Included _ (iupcone F (Singleton _ u)) (Union _ (mdowncone F (iupcone F (Singleton _ z))) (mdowncone F (Singleton _ expl))) /\
                                  ireachable u v /\
                                  mreachable v w /\
                                  ireachable w z.

Lemma correspond_Idb: forall F,
                  Idb_frame F <-> forall φ ψ, fvalid F (Idb φ ψ).
Proof.
intros F ; split ; intro Hyp.
- intros φ ψ M frameEq x y ixy Hyv ; subst.
  epose (LEM _). destruct o as [P | NP] ; [exact P | exfalso ].
  assert (exists u v w, ireachable y u /\ mreachable u v /\ ireachable v w /\ forces M w φ /\ ~ forces M w ψ).
  { epose (LEM _). destruct o as [P0 | NP0] ; [exact P0 | ].
    exfalso. apply NP. intros u ivu r mur s irs Hs ; subst. epose (LEM _). destruct o as [P1 | NP1] ; [exact P1 | ].
    exfalso. apply NP0. exists u,r,s. repeat split ; auto. }
  destruct H as (u & v & w & iyu & muv & ivw & Hw & NHw).
  destruct (Hyp _ _ _ muv ivw) as (u0 & v0 & w0 & iuu0 & cones & iu0v0 & mv0w0 & iw0w).
  intro. apply NHw. subst ; apply Expl ; auto.
  assert (forces M u0 (⬦ φ)).
  { intros v1 iu0v1.
    assert ((iupcone fra (Singleton nodes u0)) v1). exists u0. split ; auto.
    apply In_singleton.
    apply cones in H. destruct H.
    - unfold In in H. destruct H. destruct H. exists x1. split ; auto.
      apply Persistence with w ; auto. destruct H. destruct H. inversion H ; subst ; auto.
    - inversion H. destruct H0. inversion H0 ; subst. exists expl. split ; auto. apply Expl. }
  assert (~ forces M u0 (☐ ψ)).
  { intro ctr. pose (ctr _ iu0v0 _ mv0w0). apply NHw. apply Persistence with w0 ; auto. }
  apply H0. intros v1 iu0v1 u1 mv1u1. cbn in Hyv. apply Hyv with u0 v1 ; auto.
  apply ireach_tran with u ; auto.
- intros x y z mxy iyz zexpl.
  remember (fun (v : nodes) (p : nat) => (iupcone F (Singleton _ z) v /\ p = 0) \/
                                                               (~ idowncone F (Singleton _ z) v /\ p = 1) \/
                                                               v = expl) as Val.
  assert (J0: forall u v : nodes, ireachable u v -> forall p : nat, Val u p -> Val v p).
  { intros. rewrite HeqVal. rewrite HeqVal in H0. destruct H0 as [(H1 & H2)  | [(H1 & H2) | H1] ] ; subst.
    + left ; split ; auto. inversion H1. destruct H0. inversion H0 ; subst. exists x0.
       split ; auto. apply ireach_tran with u ; auto.
    + right ; left ; split ; auto. intro. apply H1. destruct H0. destruct H0. inversion H0 ; subst.
       exists x0 ; split ; auto. apply ireach_tran with v ; auto.
    + right ; right. apply ireach_expl in H ; auto. }
  assert (J1: forall p : nat, Val expl p).
  { intro p. rewrite HeqVal. right ; right ; auto. }
  pose (Build_model F Val J0 J1).
  assert (~ forces m x (☐ (# 0) --> (# 1))).
  { intro. pose (H _ (@ireach_refl _ x) _ mxy _ iyz). cbn in f.
    rewrite HeqVal in f. destruct f. 
    + left. split ; auto. exists z ; split. apply In_singleton. apply ireach_refl.
    + destruct H0 ; lia.
    + destruct H0. destruct H0. apply H0 ; exists z ; split. apply In_singleton.
       apply ireach_refl. auto. }
  assert (~ forces m x ((⬦ (# 0)) --> (☐ (# 1)))).
  { intro. apply H. pose (Hyp (#0) (#1) m eq_refl x).
    cbn in *. apply f ; auto. apply ireach_refl. }
  assert (exists s, ireachable x s /\ forces m s (⬦ # 0) /\ ~ forces m s (☐ # 1)).
  { epose (LEM _). destruct o as [P | NP] ; [exact P | ].
    exfalso. apply H0. intros v ixv Hv. epose (LEM _). destruct o as [P0 | NP0] ; [exact P0 | ].
    exfalso. apply NP. exists v ; repeat split ; auto. }
  destruct H1 as (s & Hs0 & Hs1 & Hs2).
  exists s.
  assert (exists v w, ireachable s v /\ mreachable v w /\ ~ forces m w (# 1)).
  { epose (LEM _). destruct o as [P | NP] ; [exact P | exfalso].
     apply Hs2. intros v isv w mvw. epose (LEM _). destruct o as [P0 | NP0] ; [exact P0 | exfalso].
     apply NP. exists v. exists w. repeat split ; auto. }
  destruct H1 as (v & w & isv & mvw & Hw).
  exists v. exists w. repeat split ; auto.
  + intros u Hu. destruct Hu as (t & K0 & K1). inversion K0 ; subst. unfold In.
     destruct (Hs1 _ K1) as (e & K2 & K3). destruct K3. destruct H1 ; left ; exists e ; split ; auto.
     destruct H1. exfalso ; lia. subst. right. exists expl ; split ; auto. apply In_singleton.
  + cbn in Hw. subst. epose (LEM _). destruct o as [P | NP] ; [exact P | exfalso].
    apply Hw. right. left. split ; auto. intro. apply NP. destruct H1 as (x0 & K0 & K1).
    inversion K0 ; subst ; auto.
Qed.

Lemma suff_impl_Idb  : forall F, suff_Idb_frame F -> Idb_frame F.
Proof.
intros F H x y z ixy myz Hz. destruct (H _ _ _ ixy myz) as (u & Hu0 & Hu1 & Hu2).
exists u. exists u. exists z. repeat split ; auto.
2,3: apply ireach_refl.
intros w Hw. left ; auto.
Qed.

End Idb.







Section Nd.

(* A sufficient condition to prove the axiom Nd (⬦⊥) --> ⊥ is that only expl can modally reach expl. *)

Definition suff_Nd_frame (F : frame) := forall w, mreachable w expl -> w = expl.

Lemma sufficient_Nd : forall F,
                  suff_Nd_frame F -> fvalid F Nd.
Proof.
intros F H M frameEq w v iwv Hv ; subst ; cbn in *.
apply H. destruct (Hv _ (ireach_refl v)) as (u & Hu0 & Hu1) ; subst ; auto.
Qed.

(* The axiom Nd corresponds to the following frame property: if all intuitionistic
    successors of a world w are such that the can modally reach expl, then w is expl. *)

Definition Nd_frame (F : frame) := forall w, (forall v, ireachable w v -> mreachable v expl) -> w = expl.

Lemma correspond_Nd : forall F,
                  Nd_frame F <-> fvalid F Nd.
Proof.
intro F ; split ; intro H.
- intros M frameEq w v iwv Hv ; subst ; cbn in *. apply H.
  intros. apply Hv in H0. destruct H0 as (u & Hu0 & Hu1) ; subst ; auto.
- intros w Hw.
  assert (J0: forall u v : nodes, ireachable u v -> forall p : nat, (fun (_ : nodes) (_ : nat) => True) u p -> (fun (_ : nodes) (_ : nat) => True) v p).
  intros ; auto.
  assert (J1: forall p : nat, (fun (_ : nodes) (_ : nat) => True) expl p).
  intros ; auto.
  pose (Build_model F (fun v n => True) J0 J1).
  pose (H m). unfold mvalid in m0. cbn in m0. apply m0 with w ; auto.
  apply ireach_refl. intros. exists expl ; split ; auto.
Qed.

Lemma suff_impl_Nd  : forall F, suff_Nd_frame F -> Nd_frame F.
Proof.
intros F H x Hx. apply H. apply Hx. apply ireach_refl.
Qed.

End Nd.






Section suff_Cd4.


(* While we did not present a sufficient condition for Idb, we can find one once
    both Cd and Idb are present. *)

Definition weak_Idb_frame (F : frame) := forall x y z, mreachable x y -> ireachable y z -> exists w, ireachable x w /\ mreachable w z.

Definition strong_Cd_weak_Idb_frame (F : frame) := strong_Cd_frame F /\ weak_Idb_frame F.

Lemma strong_Cd_weak_Idb_Cd_Idb : forall F, strong_Cd_weak_Idb_frame F -> (Cd_frame F /\ Idb_frame F).
Proof.
intros F H. destruct H ; split.
- apply correspond_Cd. intros. apply strong_is_suff_Cd in H. apply sufficient_Cd with (φ:=φ) (ψ:=ψ) in H ; auto.
- intros x y z mxy iyz Hz. destruct (H0 _ _ _ mxy iyz). destruct H1. exists x0. exists x0. exists z.
  repeat split ; auto. 2-3: apply ireach_refl.
  intros v Hv. destruct Hv as (w & Hw1 & Hw2). unfold In. inversion Hw1 ; subst.
  unfold suff_Cd_frame in H. destruct (H _ _ _ Hw2 H2). destruct H3. left. exists x0.
  split ; auto. exists z ; split ; auto. apply In_singleton.
Qed.

End suff_Cd4.





Section Ndb.

(* A sufficient condition to prove the axiom Nd (⬦⊥) --> (☐ ⊥) is that only expl can modally reach expl. *)

Definition suff_Ndb_frame (F : frame) := forall w, mreachable w expl -> (forall v, mreachable w v -> v = expl).

Lemma sufficient_Ndb : forall F,
                  suff_Ndb_frame F -> fvalid F Ndb.
Proof.
intros F H M frameEq w v iwv Hv u Hu x Hx ; subst ; cbn in *.
destruct (Hv _ Hu) as (y & Hy0 & Hy1) ; subst ; auto.
apply (H _ Hy0 _ Hx).
Qed.

(* The axiom Ndb corresponds to the following frame property. *)

Definition Ndb_frame (F : frame) := forall w, (forall v, ireachable w v -> mreachable v expl) -> (forall v u, ireachable w v -> mreachable v u -> u = expl).

Lemma correspond_Ndb : forall F,
                  Ndb_frame F <-> fvalid F Ndb.
Proof.
intro F ; split ; intro H.
- intros M frameEq w v iwv Hv u ivu x mux ; subst ; cbn in *.
  assert (forall z, ireachable v z -> mreachable z expl).
  { intros. destruct (Hv _ H0) as (y & Hy0 & Hy1) ; subst ; auto. }
  apply H in H0. apply H0 with u ; auto.
- intros w Hw v u iwv mvu.
  assert (J0: forall u v : nodes, ireachable u v -> forall p : nat, (fun (_ : nodes) (_ : nat) => True) u p -> (fun (_ : nodes) (_ : nat) => True) v p).
  intros ; auto.
  assert (J1: forall p : nat, (fun (_ : nodes) (_ : nat) => True) expl p).
  intros ; auto.
  pose (Build_model F (fun v n => True) J0 J1).
  pose (H m). unfold mvalid in m0. cbn in m0.
  pose (m0 eq_refl _ _ iwv). apply e with v ; auto. 2: apply ireach_refl.
  intros. exists expl ; split ; auto. apply Hw. apply ireach_tran with v ; auto.
Qed.

Lemma suff_impl_Ndb  : forall F, suff_Ndb_frame F -> Ndb_frame F.
Proof.
intros F H w Hw v u iwv mvu. apply Hw in iwv.
pose (H _ iwv). apply e ; auto.
Qed.

End Ndb.

