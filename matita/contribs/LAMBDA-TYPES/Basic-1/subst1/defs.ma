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

include "Basic-1/subst0/defs.ma".

inductive subst1 (i: nat) (v: T) (t1: T): T \to Prop \def
| subst1_refl: subst1 i v t1 t1
| subst1_single: \forall (t2: T).((subst0 i v t1 t2) \to (subst1 i v t1 t2)).

