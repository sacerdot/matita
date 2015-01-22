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

include "Basic-1/pr0/defs.ma".

inductive pr1: T \to (T \to Prop) \def
| pr1_refl: \forall (t: T).(pr1 t t)
| pr1_sing: \forall (t2: T).(\forall (t1: T).((pr0 t1 t2) \to (\forall (t3: 
T).((pr1 t2 t3) \to (pr1 t1 t3))))).

