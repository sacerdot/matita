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



inductive nat : Set \def
  | O : nat
  | S : nat \to nat.

inductive eq (A:Set): A \to A \to Prop \def
  refl: \forall x:A.eq A x x. 

inductive list (A:Set) : Set \def
  | nil : list A
  | cons : A \to list A \to list A.

let rec list_len (A:Set) (l:list A) on l \def
  match l with 
  [ nil \Rightarrow O
  | (cons a tl) \Rightarrow S (list_len A tl)].
  
theorem stupid: \forall A:Set.eq ? (list_len A (nil ?)) O.
intros.
normalize.
apply refl.
qed.
