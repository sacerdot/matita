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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/csub3/defs".

include "ty3/defs.ma".

inductive csub3 (g:G): C \to (C \to Prop) \def
| csub3_sort: \forall (n: nat).(csub3 g (CSort n) (CSort n))
| csub3_head: \forall (c1: C).(\forall (c2: C).((csub3 g c1 c2) \to (\forall 
(k: K).(\forall (u: T).(csub3 g (CHead c1 k u) (CHead c2 k u))))))
| csub3_void: \forall (c1: C).(\forall (c2: C).((csub3 g c1 c2) \to (\forall 
(b: B).((not (eq B b Void)) \to (\forall (u1: T).(\forall (u2: T).(csub3 g 
(CHead c1 (Bind Void) u1) (CHead c2 (Bind b) u2))))))))
| csub3_abst: \forall (c1: C).(\forall (c2: C).((csub3 g c1 c2) \to (\forall 
(u: T).(\forall (t: T).((ty3 g c2 u t) \to (csub3 g (CHead c1 (Bind Abst) t) 
(CHead c2 (Bind Abbr) u))))))).

