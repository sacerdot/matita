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

include "Basic-1/C/defs.ma".

inductive csubst0: nat \to (T \to (C \to (C \to Prop))) \def
| csubst0_snd: \forall (k: K).(\forall (i: nat).(\forall (v: T).(\forall (u1: 
T).(\forall (u2: T).((subst0 i v u1 u2) \to (\forall (c: C).(csubst0 (s k i) 
v (CHead c k u1) (CHead c k u2))))))))
| csubst0_fst: \forall (k: K).(\forall (i: nat).(\forall (c1: C).(\forall 
(c2: C).(\forall (v: T).((csubst0 i v c1 c2) \to (\forall (u: T).(csubst0 (s 
k i) v (CHead c1 k u) (CHead c2 k u))))))))
| csubst0_both: \forall (k: K).(\forall (i: nat).(\forall (v: T).(\forall 
(u1: T).(\forall (u2: T).((subst0 i v u1 u2) \to (\forall (c1: C).(\forall 
(c2: C).((csubst0 i v c1 c2) \to (csubst0 (s k i) v (CHead c1 k u1) (CHead c2 
k u2)))))))))).

