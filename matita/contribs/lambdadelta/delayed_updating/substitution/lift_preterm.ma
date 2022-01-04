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

include "delayed_updating/syntax/preterm.ma".
include "delayed_updating/substitution/lift.ma".

(* LIFT FOR PRETERM ***********************************************************)

definition lift_preterm (f) (t): preterm ≝
           λp. ∃∃r. r ϵ t & p = ↑[f]r.

interpretation
  "lift (preterm)"
  'UpArrow f t = (lift_preterm f t).
