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

include "Basic-1/C/defs.ma".

definition fweight:
 C \to (T \to nat)
\def
 \lambda (c: C).(\lambda (t: T).(plus (cweight c) (tweight t))).

definition flt:
 C \to (T \to (C \to (T \to Prop)))
\def
 \lambda (c1: C).(\lambda (t1: T).(\lambda (c2: C).(\lambda (t2: T).(lt 
(fweight c1 t1) (fweight c2 t2))))).

