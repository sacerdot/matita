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


include "coq.ma".

inductive stupidtype: Set \def
  | Base : stupidtype
  | Next : stupidtype \to stupidtype
  | Pair : stupidtype \to stupidtype \to stupidtype.
  
alias symbol "eq" (instance 0) = "Coq's leibnitz's equality".
alias symbol "exists" (instance 0) = "Coq's exists".
alias symbol "or" (instance 0) = "Coq's logical or".
alias num (instance 0) = "natural number".
alias id "True" = "cic:/Coq/Init/Logic/True.ind#xpointer(1/1)".
alias id "refl_equal" = "cic:/Coq/Init/Logic/eq.ind#xpointer(1/1/1)".
  
theorem serious:
  \forall a:stupidtype.
    a = Base 
  \lor 
    (\exists b:stupidtype.a = Next b) 
  \lor 
    (\exists c,d:stupidtype.a = Pair c d).
intros.
elim a.
clear a.left.left.
  reflexivity.
clear H.clear a.left.right.
  exists.exact s.reflexivity.
clear H.clear H1.clear a.right.
  exists.exact s.exists.exact s1.reflexivity.  
qed.

theorem t: 0=0 \to stupidtype.
 intros; constructor 1.
qed.

(* In this test "elim t" should open a new goal 0=0 and put it in the *)
(* goallist so that the THEN tactical closes it using reflexivity.    *)
theorem foo: let ax \def refl_equal ? 0 in t ax = t ax.
 elim t; reflexivity.
qed.

(* This test shows a bug where elim opens a new unus{ed,eful} goal *)

alias symbol "eq" (instance 0) = "Coq's leibnitz's equality".
alias id "O" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1/1)".

inductive sum (n:nat) : nat \to nat \to Set \def
  k: \forall x,y. n = x + y \to sum n x y.
  
theorem t': \forall x,y. \forall H: sum x y O.
          match H with [ (k a b p) \Rightarrow a ] = x.
 intros.
 cut (y = y \to O = O \to match H with [ (k a b p) \Rightarrow a] = x).
 apply Hcut; reflexivity.
 apply
  (sum_ind ?
    (\lambda a,b,K. y=a \to O=b \to
        match K with [ (k a b p) \Rightarrow a ] = x)
     ? ? ? H).
 simplify. intros.
 generalize in match H1.
 rewrite < H2; rewrite < H3.intro.
 rewrite > H4.autobatch library.
qed.
