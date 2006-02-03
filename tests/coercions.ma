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

set "baseuri" "cic:/matita/tests/coercions/".
include "legacy/coq.ma".

inductive pos: Set \def
| one : pos
| next : pos \to pos.

inductive nat:Set \def
| O : nat
| S : nat \to nat.

inductive int: Set \def
| positive: nat \to int
| negative : nat \to int.

inductive empty : Set \def .

let rec pos2nat x \def 
  match x with  
  [ one \Rightarrow (S O)
  | (next z) \Rightarrow S (pos2nat z)].

definition nat2int \def \lambda x. positive x.

coercion cic:/matita/tests/coercions/pos2nat.con.

coercion cic:/matita/tests/coercions/nat2int.con.

definition fst \def \lambda x,y:int.x.

theorem a: fst O one = fst (positive O) (next one).
reflexivity.
qed.

definition double: 
  \forall f:int \to int. pos \to int 
\def 
  \lambda f:int \to int. \lambda x : pos .f (nat2int x).
  
definition double1: 
  \forall f:int \to int. pos \to int 
\def 
  \lambda f:int \to int. \lambda x : pos .f (pos2nat x).

definition double2: 
  \forall f:int \to int. pos \to int 
\def 
  \lambda f:int \to int. \lambda x : pos .f (nat2int (pos2nat x)).
  
  
