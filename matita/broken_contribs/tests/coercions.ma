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



include "nat/compare.ma".
include "nat/times.ma".

inductive pos: Set \def
| one : pos
| next : pos \to pos.

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

(* This used to test eq_f as a coercion. However, posing both eq_f and sym_eq
   as coercions made the qed time of some TPTP problems reach infty.
   Thus eq_f is no longer a coercion (nor is sym_eq).
theorem coercion_svelta : \forall T,S:Type.\forall f:T \to S.\forall x,y:T.x=y \to f y = f x.
  intros.
  apply ((\lambda h:f y = f x.h) H).
qed.
*)

variant pos2nat' : ? \def pos2nat.

inductive initial: Set \def iii : initial.

definition i2pos: ? \def \lambda x:initial.one.

coercion cic:/matita/tests/coercions/i2pos.con.

coercion cic:/matita/tests/coercions/pos2nat'.con.

inductive listn (A:Type) : nat \to Type \def
 | Nil : listn A O
 | Next : \forall n.\forall l:listn A n.\forall a:A.listn A (S n).
 
definition if : \forall A:Type.\forall b:bool.\forall a,c:A.A \def
  \lambda A,b,a,c.
  match b with
  [ true \Rightarrow a
  | false \Rightarrow c].  
 
let rec ith (A:Type) (n,m:nat) (dummy:A) (l:listn A n) on l \def
  match l with
  [ Nil \Rightarrow dummy
  | (Next w l x) \Rightarrow if A (eqb w m) x (ith A w m dummy l)].  

definition listn2function: 
  \forall A:Type.\forall dummy:A.\forall n.listn A n \to nat \to A
\def
  \lambda A,dummy,n,l,m.ith A n m dummy l.
  
definition natlist2map: ? \def listn2function nat O.
  
coercion cic:/matita/tests/coercions/natlist2map.con 1.
definition map:  \forall n:nat.\forall l:listn nat n. nat \to nat \def
  \lambda n:nat.\lambda l:listn nat n.\lambda m:nat.l m.
  
definition church: nat \to nat \to nat \def times.

coercion cic:/matita/tests/coercions/church.con 1.
lemma foo0 : ∀n:nat. n n = n * n.
intros; reflexivity;
qed.
lemma foo01 : ∀n:nat. n n n = n * n * n.
intros; reflexivity;
qed.

definition mapmult:  \forall n:nat.\forall l:listn nat n. nat \to nat \to nat \def
  \lambda n:nat.\lambda l:listn nat n.\lambda m,o:nat.
  l (m m) o (o o o).
  
lemma foo : ∀n:nat. n n n n n n = n * n * n * n * n * n.
intros; reflexivity;
qed.

axiom f : nat → nat.

lemma foo1 : ∀n:nat. f n n = f n * n.

axiom T0 : Type.
axiom T1 : Type.
axiom T2 : Type.
axiom T3 : Type.

axiom c1 : T0 -> T1.
axiom c2 : T1 -> T2.
axiom c3 : T2 -> T3.
axiom c4 : T2 -> T1.

coercion cic:/matita/tests/coercions/c1.con.
coercion cic:/matita/tests/coercions/c2.con.
coercion cic:/matita/tests/coercions/c3.con.
coercion cic:/matita/tests/coercions/c4.con.



  
  
 