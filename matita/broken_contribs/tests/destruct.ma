(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)



include "logic/equality.ma".
include "nat/nat.ma".
include "datatypes/constructors.ma".

theorem stupid:
  (S O) = O \to (\forall p:Prop. p \to Not p).
  intros.
  generalize in match I.
  destruct H.
qed.

inductive bar_list (A:Set): Set \def
  | bar_nil: bar_list A
  | bar_cons: A \to bar_list A \to bar_list A.

theorem stupid2:
  \forall A:Set.\forall x:A.\forall l:bar_list A.
  bar_nil A = bar_cons A x l \to False.
  intros.
  destruct H.
qed.

inductive dt (A:Type): Type \to Type \def
 | k1: \forall T:Type. dt A T
 | k2: \forall T:Type. \forall T':Type. dt A (T \to T').
 
theorem stupid3:
 k1 False (False → True) = k2 False False True → False.
 intros;
 destruct H.
qed.

inductive dddt (A:Type): Type \to Type \def
 | kkk1: dddt A nat
 | kkk2: dddt A nat.
 
theorem stupid4: kkk1 False = kkk2 False \to False.
 intros;
 destruct H.
qed.

theorem recursive: S (S (S O)) = S (S O) \to False.
 intros;
 destruct H.
qed.

inductive complex (A,B : Type) : B → A → Type ≝
| C1 : ∀x:nat.∀a:A.∀b:B. complex A B b a
| C2 : ∀a,a1:A.∀b,b1:B.∀x:nat. complex A B b1 a1 → complex A B b a.

theorem recursive1: ∀ x,y : nat. 
  (C1 ? ? O     (Some ? x) y) = 
  (C1 ? ? (S O) (Some ? x) y) → False.
intros; destruct H.
qed.

theorem recursive2: ∀ x,y,z,t : nat. 
  (C1 ? ? t (Some ? x) y) = 
  (C1 ? ? z (Some ? x) y) → t=z.
intros; destruct H; reflexivity.
qed.

theorem recursive3: ∀ x,y,z,t : nat. 
  C2 ? ? (None ?) ? (S O) ? z (C1 ? ? (S O) (Some ? x) y) = 
  C2 ? ? (None ?) ? (S O) ? t (C1 ? ? (S O) (Some ? x) y) → z=t.
intros; destruct H; reflexivity.
qed.

theorem recursive4: ∀ x,y,z,t : nat. 
  C2 ? ? (None ?) ? (S O) ? z (C1 ? ? (S O) (Some ? z) y) = 
  C2 ? ? (None ?) ? (S O) ? t (C1 ? ? (S O) (Some ? x) y) → z=t.
intros; destruct H; reflexivity.
qed.

theorem recursive2: ∀ x,y : nat. 
  C2 ? ? (None ?) ? (S O) ? O (C1 ? ? O     (Some ? x) y) = 
  C2 ? ? (None ?) ? (S O) ? O (C1 ? ? (S O) (Some ? x) y) → False.
intros; destruct H.
qed.