Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Ensembles.

Require Import general_export.

Require Import im_syntax.

(* We define here the intuitionistic axioms. *)

Inductive IAxioms (F : form) : Prop :=
 | IA1 A B : F = (A --> (B --> A)) -> IAxioms F
 | IA2 A B C : F = (A --> (B --> C)) --> ((A --> B) --> (A --> C)) -> IAxioms F
 | IA3 A B : F = A --> (Or A B) -> IAxioms F
 | IA4 A B : F = B --> (Or A B) -> IAxioms F
 | IA5 A B C : F = (A --> C) --> ((B --> C) --> ((Or A B) --> C)) -> IAxioms F
 | IA6 A B : F = (And A B) --> A -> IAxioms F
 | IA7 A B : F = (And A B) --> B -> IAxioms F
 | IA8 A B C : F = (A --> B) --> ((A --> C) --> (A --> (And B C))) -> IAxioms F
 | IA9 A : F = Bot --> A -> IAxioms F.

(* We then define the modal axioms. *)

Inductive MAxioms (F : form) : Prop :=
 | MAK1 A B : F = Box (A --> B) --> (Box A --> Box B) -> MAxioms F
 | MAK2 A B : F = Box (A --> B) --> (Diam A --> Diam B) -> MAxioms F.

Definition Axioms (A : form) : Prop := IAxioms A \/ MAxioms A.

(* At last we can define our calculus CKH. *)

Inductive CKH_prv : (form -> Prop) -> form -> Prop :=
  | Id Γ A : In _ Γ A -> CKH_prv Γ A
  | Ax Γ A : Axioms A -> CKH_prv Γ A
  | MP Γ A B : CKH_prv Γ (A --> B) ->  CKH_prv Γ A -> CKH_prv Γ B
  | Nec Γ A : CKH_prv (Empty_set _) A -> CKH_prv Γ (Box A).
