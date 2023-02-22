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



inductive pos: Set \def
| one : pos
| next : pos \to pos.

inductive nat:Set \def
| O : nat
| S : nat \to nat.

definition pos2nat : pos \to nat  \def 
     \lambda x:pos . match x with  
      [ one \Rightarrow O 
      | (next z) \Rightarrow O]. 

inductive empty (x:nat) : nat \to Set \def .

definition empty2nat : (empty O O) \to nat  \def
  \lambda x : (empty O O). S (match x in empty with []).

inductive le (n:nat) : nat \to Prop \def
  | le_n : le n n
  | le_S : \forall m:nat. le n m \to le n (S m).

inductive True : Prop \def
 I : True.

definition r : True \def
 match (le_n O) with
  [ le_n \Rightarrow I
  | (le_S y p') \Rightarrow I ].

inductive Prod (A,B:Set): Set \def
pair : A \to B \to Prod A B.

definition fst : \forall A,B:Set. (Prod A B) \to A \def
\lambda A,B:Set. \lambda p:(Prod A B). match p with
[(pair a b) \Rightarrow a].
