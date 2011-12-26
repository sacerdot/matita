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

include "Basic_2/substitution/ldrop.ma".
include "Basic_2/unfold/lifts.ma".

(* GENERIC LOCAL ENVIRONMENT SLICING ****************************************)

inductive ldrops: list2 nat nat → relation lenv ≝
| ldrops_nil : ∀L. ldrops ⟠ L L
| ldrops_cons: ∀L1,L,L2,des,d,e.
               ⇓[d,e] L1 ≡ L → ldrops des L L2 → ldrops ({d, e} :: des) L1 L2
.

interpretation "generic local environment slicing"
   'RDrop des T1 T2 = (ldrops des T1 T2).
