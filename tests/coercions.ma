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
include "nat/nat.ma".

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
  
coercion cic:/matita/logic/equality/eq_f.con.  
coercion cic:/matita/logic/equality/eq_f1.con.
variant xxx : ? \def eq_f.
coercion cic:/matita/tests/coercions/xxx.con.

theorem coercion_svelta : \forall T,S:Type.\forall f:T \to S.\forall x,y:T.x=y \to f y = f x.
  intros.
  apply ((\lambda h:f y = f x.h) H).
qed.

variant pos2nat' : ? \def pos2nat.

coercion cic:/matita/tests/coercions/xxx.con.

inductive initial: Set \def iii : initial.

definition i2pos: ? \def \lambda x:initial.one.

coercion cic:/matita/tests/coercions/i2pos.con.

coercion cic:/matita/tests/coercions/pos2nat'.con.


