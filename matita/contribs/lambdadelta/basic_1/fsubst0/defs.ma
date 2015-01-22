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

inductive fsubst0 (i: nat) (v: T) (c1: C) (t1: T): C \to (T \to Prop) \def
| fsubst0_snd: \forall (t2: T).((subst0 i v t1 t2) \to (fsubst0 i v c1 t1 c1 
t2))
| fsubst0_fst: \forall (c2: C).((csubst0 i v c1 c2) \to (fsubst0 i v c1 t1 c2 
t1))
| fsubst0_both: \forall (t2: T).((subst0 i v t1 t2) \to (\forall (c2: 
C).((csubst0 i v c1 c2) \to (fsubst0 i v c1 t1 c2 t2)))).

