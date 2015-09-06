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

include "basic_1/pr1/defs.ma".

implied let rec pr1_ind (P: (T \to (T \to Prop))) (f: (\forall (t: T).(P t 
t))) (f0: (\forall (t2: T).(\forall (t1: T).((pr0 t1 t2) \to (\forall (t3: 
T).((pr1 t2 t3) \to ((P t2 t3) \to (P t1 t3)))))))) (t: T) (t0: T) (p: pr1 t 
t0) on p: P t t0 \def match p with [(pr1_refl t1) \Rightarrow (f t1) | 
(pr1_sing t2 t1 p0 t3 p1) \Rightarrow (f0 t2 t1 p0 t3 p1 ((pr1_ind P f f0) t2 
t3 p1))].

