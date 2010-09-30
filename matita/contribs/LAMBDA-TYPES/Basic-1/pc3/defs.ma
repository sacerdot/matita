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

include "Basic-1/pr3/defs.ma".

definition pc3:
 C \to (T \to (T \to Prop))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(ex2 T (\lambda (t: T).(pr3 
c t1 t)) (\lambda (t: T).(pr3 c t2 t))))).

inductive pc3_left (c: C): T \to (T \to Prop) \def
| pc3_left_r: \forall (t: T).(pc3_left c t t)
| pc3_left_ur: \forall (t1: T).(\forall (t2: T).((pr2 c t1 t2) \to (\forall 
(t3: T).((pc3_left c t2 t3) \to (pc3_left c t1 t3)))))
| pc3_left_ux: \forall (t1: T).(\forall (t2: T).((pr2 c t1 t2) \to (\forall 
(t3: T).((pc3_left c t1 t3) \to (pc3_left c t2 t3))))).

