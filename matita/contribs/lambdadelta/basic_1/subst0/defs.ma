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

include "Basic-1/lift/defs.ma".

inductive subst0: nat \to (T \to (T \to (T \to Prop))) \def
| subst0_lref: \forall (v: T).(\forall (i: nat).(subst0 i v (TLRef i) (lift 
(S i) O v)))
| subst0_fst: \forall (v: T).(\forall (u2: T).(\forall (u1: T).(\forall (i: 
nat).((subst0 i v u1 u2) \to (\forall (t: T).(\forall (k: K).(subst0 i v 
(THead k u1 t) (THead k u2 t))))))))
| subst0_snd: \forall (k: K).(\forall (v: T).(\forall (t2: T).(\forall (t1: 
T).(\forall (i: nat).((subst0 (s k i) v t1 t2) \to (\forall (u: T).(subst0 i 
v (THead k u t1) (THead k u t2))))))))
| subst0_both: \forall (v: T).(\forall (u1: T).(\forall (u2: T).(\forall (i: 
nat).((subst0 i v u1 u2) \to (\forall (k: K).(\forall (t1: T).(\forall (t2: 
T).((subst0 (s k i) v t1 t2) \to (subst0 i v (THead k u1 t1) (THead k u2 
t2)))))))))).

