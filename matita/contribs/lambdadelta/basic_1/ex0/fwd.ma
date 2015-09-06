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

(* This file was automatically generated: do not edit *********************)

include "basic_1/ex0/defs.ma".

implied let rec leqz_ind (P: (A \to (A \to Prop))) (f: (\forall (h1: 
nat).(\forall (h2: nat).(\forall (n1: nat).(\forall (n2: nat).((eq nat (plus 
h1 n2) (plus h2 n1)) \to (P (ASort h1 n1) (ASort h2 n2)))))))) (f0: (\forall 
(a1: A).(\forall (a2: A).((leqz a1 a2) \to ((P a1 a2) \to (\forall (a3: 
A).(\forall (a4: A).((leqz a3 a4) \to ((P a3 a4) \to (P (AHead a1 a3) (AHead 
a2 a4))))))))))) (a: A) (a0: A) (l: leqz a a0) on l: P a a0 \def match l with 
[(leqz_sort h1 h2 n1 n2 e) \Rightarrow (f h1 h2 n1 n2 e) | (leqz_head a1 a2 
l0 a3 a4 l1) \Rightarrow (f0 a1 a2 l0 ((leqz_ind P f f0) a1 a2 l0) a3 a4 l1 
((leqz_ind P f f0) a3 a4 l1))].

