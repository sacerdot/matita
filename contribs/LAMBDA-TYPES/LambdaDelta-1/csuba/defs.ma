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

include "LambdaDelta-1/arity/defs.ma".

inductive csuba (g: G): C \to (C \to Prop) \def
| csuba_sort: \forall (n: nat).(csuba g (CSort n) (CSort n))
| csuba_head: \forall (c1: C).(\forall (c2: C).((csuba g c1 c2) \to (\forall 
(k: K).(\forall (u: T).(csuba g (CHead c1 k u) (CHead c2 k u))))))
| csuba_abst: \forall (c1: C).(\forall (c2: C).((csuba g c1 c2) \to (\forall 
(t: T).(\forall (a: A).((arity g c1 t (asucc g a)) \to (\forall (u: 
T).((arity g c2 u a) \to (csuba g (CHead c1 (Bind Abst) t) (CHead c2 (Bind 
Abbr) u))))))))).

