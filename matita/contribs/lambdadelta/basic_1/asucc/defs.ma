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

include "basic_1/A/defs.ma".

include "basic_1/G/defs.ma".

rec definition asucc (g: G) (l: A) on l: A \def match l with [(ASort n0 n) 
\Rightarrow (match n0 with [O \Rightarrow (ASort O (next g n)) | (S h) 
\Rightarrow (ASort h n)]) | (AHead a1 a2) \Rightarrow (AHead a1 (asucc g 
a2))].

