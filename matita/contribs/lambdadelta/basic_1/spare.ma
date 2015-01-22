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

include "Basic-1/theory.ma".

axiom pc3_gen_appls_sort_abst:
 \forall (c: C).(\forall (vs: TList).(\forall (w: T).(\forall (u: T).(\forall 
(n: nat).((pc3 c (THeads (Flat Appl) vs (TSort n)) (THead (Bind Abst) w u)) 
\to False)))))
.

axiom pc3_gen_appls_lref_abst:
 \forall (c: C).(\forall (d: C).(\forall (v: T).(\forall (i: nat).((getl i c 
(CHead d (Bind Abst) v)) \to (\forall (vs: TList).(\forall (w: T).(\forall 
(u: T).((pc3 c (THeads (Flat Appl) vs (TLRef i)) (THead (Bind Abst) w u)) \to 
False))))))))
.

axiom pc3_gen_appls_lref_sort:
 \forall (c: C).(\forall (d: C).(\forall (v: T).(\forall (i: nat).((getl i c 
(CHead d (Bind Abst) v)) \to (\forall (vs: TList).(\forall (ws: 
TList).(\forall (n: nat).((pc3 c (THeads (Flat Appl) vs (TLRef i)) (THeads 
(Flat Appl) ws (TSort n))) \to False))))))))
.

