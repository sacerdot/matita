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

include "ground/relocation/f2/fr2_nat.ma".

(* NON-NEGATIVE APPLICATION FOR FINITE RELOCATION MAPS WITH PAIRS ***********)

(* Main constructions *******************************************************)

(*** at_mono *)
theorem fr2_nat_mono (f) (l):
        ∀l1. ＠§❨l, f❩ ≘ l1 → ∀l2. ＠§❨l, f❩ ≘ l2 → l1 = l2.
#f #l #l1 #H elim H -f -l -l1
[ #l #x #H <(fr2_nat_inv_empty … H) -x //
| #f #d #h #l #l1 #Hld #_ #IH #x #H
  lapply (fr2_nat_inv_lcons_lt … H Hld) -H -Hld /2 width=1 by/
| #f #d #h #l #l1 #Hdl #_ #IH #x #H
  lapply (fr2_nat_inv_lcons_ge … H Hdl) -H -Hdl /2 width=1 by/
]
qed-.
