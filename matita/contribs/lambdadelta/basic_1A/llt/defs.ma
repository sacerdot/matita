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

include "basic_1A/A/defs.ma".

rec definition lweight (a: A) on a: nat \def match a with [(ASort _ _) 
\Rightarrow O | (AHead a1 a2) \Rightarrow (S (plus (lweight a1) (lweight 
a2)))].

definition llt:
 A \to (A \to Prop)
\def
 \lambda (a1: A).(\lambda (a2: A).(lt (lweight a1) (lweight a2))).

