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

include "Ground-1/preamble.ma".

definition blt:
 nat \to (nat \to bool)
\def
 let rec blt (m: nat) (n: nat) on n: bool \def (match n with [O \Rightarrow 
false | (S n0) \Rightarrow (match m with [O \Rightarrow true | (S m0) 
\Rightarrow (blt m0 n0)])]) in blt.

