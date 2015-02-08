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

include "basic_1/getl/defs.ma".

definition cimp:
 C \to (C \to Prop)
\def
 \lambda (c1: C).(\lambda (c2: C).(\forall (b: B).(\forall (d1: C).(\forall 
(w: T).(\forall (h: nat).((getl h c1 (CHead d1 (Bind b) w)) \to (let TMP_3 
\def (\lambda (d2: C).(let TMP_1 \def (Bind b) in (let TMP_2 \def (CHead d2 
TMP_1 w) in (getl h c2 TMP_2)))) in (ex C TMP_3)))))))).

