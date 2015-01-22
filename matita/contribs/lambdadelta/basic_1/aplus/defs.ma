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

include "Basic-1/asucc/defs.ma".

definition aplus:
 G \to (A \to (nat \to A))
\def
 let rec aplus (g: G) (a: A) (n: nat) on n: A \def (match n with [O 
\Rightarrow a | (S n0) \Rightarrow (asucc g (aplus g a n0))]) in aplus.

