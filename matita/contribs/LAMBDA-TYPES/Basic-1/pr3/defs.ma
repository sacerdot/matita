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

include "Basic-1/pr2/defs.ma".

inductive pr3 (c: C): T \to (T \to Prop) \def
| pr3_refl: \forall (t: T).(pr3 c t t)
| pr3_sing: \forall (t2: T).(\forall (t1: T).((pr2 c t1 t2) \to (\forall (t3: 
T).((pr3 c t2 t3) \to (pr3 c t1 t3))))).

