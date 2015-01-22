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

include "Basic-1/A/defs.ma".

include "Basic-1/G/defs.ma".

definition asucc:
 G \to (A \to A)
\def
 let rec asucc (g: G) (l: A) on l: A \def (match l with [(ASort n0 n) 
\Rightarrow (match n0 with [O \Rightarrow (ASort O (next g n)) | (S h) 
\Rightarrow (ASort h n)]) | (AHead a1 a2) \Rightarrow (AHead a1 (asucc g 
a2))]) in asucc.

