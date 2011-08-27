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

include "Ground-2/list.ma".

(* SORT HIERARCHY ***********************************************************)

(* sort hierarchy specifications *)
record sh: Type[0] ≝ {
   next: nat → nat;        (* next sort in the hierarchy *)
   next_lt: ∀k. k < next k (* strict monotonicity condition *)
}.
