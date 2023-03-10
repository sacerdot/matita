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

include "basic_1A/A/defs.ma".

implied rec lemma A_rect (P: (A \to Type[0])) (f: (\forall (n: nat).(\forall 
(n0: nat).(P (ASort n n0))))) (f0: (\forall (a: A).((P a) \to (\forall (a0: 
A).((P a0) \to (P (AHead a a0))))))) (a: A) on a: P a \def match a with 
[(ASort n n0) \Rightarrow (f n n0) | (AHead a0 a1) \Rightarrow (f0 a0 
((A_rect P f f0) a0) a1 ((A_rect P f f0) a1))].

implied lemma A_ind:
 \forall (P: ((A \to Prop))).(((\forall (n: nat).(\forall (n0: nat).(P (ASort 
n n0))))) \to (((\forall (a: A).((P a) \to (\forall (a0: A).((P a0) \to (P 
(AHead a a0))))))) \to (\forall (a: A).(P a))))
\def
 \lambda (P: ((A \to Prop))).(A_rect P).

