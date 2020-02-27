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

include "ground/relocation/rtmap_sor.ma".

(* RELOCATION N-STREAM ******************************************************)

axiom union: rtmap → rtmap → rtmap.

interpretation "union (nstream)"
   'union f1 f2 = (union f1 f2).

(* Specific properties on sor ***********************************************)

axiom sor_total: ∀f1,f2. f1 ⋓ f2 ≘ f1 ∪ f2.
