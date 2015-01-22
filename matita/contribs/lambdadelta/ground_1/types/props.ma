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

include "Ground-1/types/defs.ma".

theorem ex2_sym:
 \forall (A: Set).(\forall (P: ((A \to Prop))).(\forall (Q: ((A \to 
Prop))).((ex2 A (\lambda (x: A).(P x)) (\lambda (x: A).(Q x))) \to (ex2 A 
(\lambda (x: A).(Q x)) (\lambda (x: A).(P x))))))
\def
 \lambda (A: Set).(\lambda (P: ((A \to Prop))).(\lambda (Q: ((A \to 
Prop))).(\lambda (H: (ex2 A (\lambda (x: A).(P x)) (\lambda (x: A).(Q 
x)))).(ex2_ind A (\lambda (x: A).(P x)) (\lambda (x: A).(Q x)) (ex2 A 
(\lambda (x: A).(Q x)) (\lambda (x: A).(P x))) (\lambda (x: A).(\lambda (H0: 
(P x)).(\lambda (H1: (Q x)).(ex_intro2 A (\lambda (x0: A).(Q x0)) (\lambda 
(x0: A).(P x0)) x H1 H0)))) H)))).
(* COMMENTS
Initial nodes: 91
END *)

