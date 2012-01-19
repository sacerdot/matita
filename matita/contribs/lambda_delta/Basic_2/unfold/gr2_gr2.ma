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

include "Basic_2/unfold/gr2.ma".

(* GENERIC RELOCATION WITH PAIRS ********************************************)

(* Main properties **********************************************************)

axiom at_mono: ∀des,i,i1. @[i] des ≡ i1 → ∀i2. @[i] des ≡ i2 → i1 = i2. 
