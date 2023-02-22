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


alias symbol "eq" (instance 0) = "Coq's leibnitz's equality".
alias id "O" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1/1)".

inductive sum (n:nat) : nat \to nat \to Set \def
  k: \forall x,y. n = x + y \to sum n x y.



  
theorem t: \forall x,y. \forall H: sum x y O.
          match H with [ (k a b p) \Rightarrow a ] = x.
 intros.
 inversion H.
 
 (*
 cut (y = y \to O = O \to match H with [ (k a b p) \Rightarrow a] = x).
 apply Hcut; reflexivity.
 apply
  (sum_ind ?
    (\lambda a,b,K. y=a \to O=b \to
        match K with [ (k a b p) \Rightarrow a ] = x)
     ? ? ? H).
 goal 16.*)
 simplify. intros.
 generalize in match H1.
 rewrite < H2; rewrite < H3.intro.
 rewrite > H4.autobatch library.
qed.

theorem t1: \forall x,y. sum x y O \to x = y.
intros.

(*
cut y=y \to O=O \to x = y.
apply Hcut.reflexivity. reflexivity.
apply (sum_ind ? (\lambda a,b,K. y=a \to O=b \to x=a) ? ? ? s).*)

(*apply (sum_ind ? (\lambda a,b,K. y = a \to O = b \to  x = a) ? ? ? s).*)
inversion s.
intros.simplify.
intros.
rewrite > H. rewrite < H2.  autobatch library.
qed.
