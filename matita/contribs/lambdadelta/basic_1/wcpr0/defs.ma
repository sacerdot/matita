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

include "Basic-1/C/defs.ma".

inductive wcpr0: C \to (C \to Prop) \def
| wcpr0_refl: \forall (c: C).(wcpr0 c c)
| wcpr0_comp: \forall (c1: C).(\forall (c2: C).((wcpr0 c1 c2) \to (\forall 
(u1: T).(\forall (u2: T).((pr0 u1 u2) \to (\forall (k: K).(wcpr0 (CHead c1 k 
u1) (CHead c2 k u2)))))))).

