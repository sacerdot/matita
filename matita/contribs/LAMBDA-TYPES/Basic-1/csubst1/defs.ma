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

include "Basic-1/csubst0/defs.ma".

inductive csubst1 (i: nat) (v: T) (c1: C): C \to Prop \def
| csubst1_refl: csubst1 i v c1 c1
| csubst1_sing: \forall (c2: C).((csubst0 i v c1 c2) \to (csubst1 i v c1 c2)).

