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

include "Basic-1/G/defs.ma".

definition next_plus:
 G \to (nat \to (nat \to nat))
\def
 let rec next_plus (g: G) (n: nat) (i: nat) on i: nat \def (match i with [O 
\Rightarrow n | (S i0) \Rightarrow (next g (next_plus g n i0))]) in next_plus.

