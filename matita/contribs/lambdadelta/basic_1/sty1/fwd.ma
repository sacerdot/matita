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

include "basic_1/sty1/defs.ma".

implied rec lemma sty1_ind (g: G) (c: C) (t1: T) (P: (T \to Prop)) (f: 
(\forall (t2: T).((sty0 g c t1 t2) \to (P t2)))) (f0: (\forall (t: T).((sty1 
g c t1 t) \to ((P t) \to (\forall (t2: T).((sty0 g c t t2) \to (P t2))))))) 
(t: T) (s0: sty1 g c t1 t) on s0: P t \def match s0 with [(sty1_sty0 t2 s1) 
\Rightarrow (f t2 s1) | (sty1_sing t0 s1 t2 s2) \Rightarrow (f0 t0 s1 
((sty1_ind g c t1 P f f0) t0 s1) t2 s2)].

