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

include "basic_2/rt_computation/jsx.ma".

(* COMPATIBILITY OF STRONG NORMALIZATION FOR UNBOUND RT-TRANSITION **********)

(* Main properties **********************************************************)

theorem jsx_fix (h) (G):
        ∀f,L1,L. G ⊢ L1 ⊒[h,f] L → ∀L2. G ⊢ L ⊒[h,f] L2 → L = L2.
#h #G #f #L1 #L #H elim H -f -L1 -L
[ #f #L2 #H
  >(jsx_inv_atom_sn … H) -L2 //
| #f #I #K1 #K2 #_ #IH #L2 #H
  elim (jsx_inv_push_sn … H) -H /3 width=1 by eq_f2/
| #f #I #K1 #K2 #_ #IH #L2 #H
  elim (jsx_inv_unit_sn … H) -H /3 width=1 by eq_f2/
| #f #I #K1 #K2 #V #_ #_ #IH #L2 #H
  elim (jsx_inv_unit_sn … H) -H /3 width=1 by eq_f2/
]
qed-.

theorem jsx_trans (h) (G): ∀f. Transitive … (jsx h G f).
#h #G #f #L1 #L #H1 #L2 #H2
<(jsx_fix … H1 … H2) -L2 //
qed-.
