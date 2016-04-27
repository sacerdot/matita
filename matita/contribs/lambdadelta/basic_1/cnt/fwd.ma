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

include "basic_1/cnt/defs.ma".

implied rec lemma cnt_ind (P: (T \to Prop)) (f: (\forall (n: nat).(P (TSort 
n)))) (f0: (\forall (t: T).((cnt t) \to ((P t) \to (\forall (k: K).(\forall 
(v: T).(P (THead k v t)))))))) (t: T) (c: cnt t) on c: P t \def match c with 
[(cnt_sort n) \Rightarrow (f n) | (cnt_head t0 c0 k v) \Rightarrow (f0 t0 c0 
((cnt_ind P f f0) t0 c0) k v)].

