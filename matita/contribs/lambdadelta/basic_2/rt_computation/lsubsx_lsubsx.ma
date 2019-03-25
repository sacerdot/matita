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

include "basic_2/rt_computation/lsubsx.ma".

(* CLEAR OF STRONGLY NORMALIZING ENTRIES FOR UNBOUND RT-TRANSITION **********)

(* Main properties **********************************************************)

theorem lsubsx_fix: ∀h,f,G,L1,L. G ⊢ L1 ⊆ⓧ[h, f] L →
                    ∀L2. G ⊢ L ⊆ⓧ[h, f] L2 → L = L2.
#h #f #G #L1 #L #H elim H -f -L1 -L
[ #f #L2 #H
  >(lsubsx_inv_atom_sn … H) -L2 //
| #f #I #K1 #K2 #_ #IH #L2 #H
  elim (lsubsx_inv_push_sn … H) -H /3 width=1 by eq_f2/
| #f #I #K1 #K2 #_ #IH #L2 #H
  elim (lsubsx_inv_unit_sn … H) -H /3 width=1 by eq_f2/
| #f #I #K1 #K2 #V #_ #_ #IH #L2 #H
  elim (lsubsx_inv_unit_sn … H) -H /3 width=1 by eq_f2/
]
qed-.

theorem lsubsx_trans: ∀h,f,G. Transitive … (lsubsx h G f).
#h #f #G #L1 #L #H1 #L2 #H2
<(lsubsx_fix … H1 … H2) -L2 //
qed-.
