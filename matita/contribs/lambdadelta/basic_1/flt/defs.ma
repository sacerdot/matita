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

include "basic_1/C/defs.ma".

definition fweight:
 C \to (T \to nat)
\def
 \lambda (c: C).(\lambda (t: T).(let TMP_1 \def (cweight c) in (let TMP_2 
\def (tweight t) in (plus TMP_1 TMP_2)))).

definition flt:
 C \to (T \to (C \to (T \to Prop)))
\def
 \lambda (c1: C).(\lambda (t1: T).(\lambda (c2: C).(\lambda (t2: T).(let 
TMP_1 \def (fweight c1 t1) in (let TMP_2 \def (fweight c2 t2) in (lt TMP_1 
TMP_2)))))).

