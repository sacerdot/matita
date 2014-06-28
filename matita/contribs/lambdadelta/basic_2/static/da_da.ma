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

include "basic_2/static/da_lift.ma".

(* DEGREE ASSIGNMENT FOR TERMS **********************************************)

(* Main properties **********************************************************)

theorem da_mono: ∀h,g,G,L,T,l1. ⦃G, L⦄ ⊢ T ▪[h, g] l1 →
                 ∀l2. ⦃G, L⦄ ⊢ T ▪[h, g] l2 → l1 = l2.
#h #g #G #L #T #l1 #H elim H -G -L -T -l1
[ #G #L #k #l1 #Hkl1 #l2 #H
  lapply (da_inv_sort … H) -G -L #Hkl2
  >(deg_mono … Hkl2 … Hkl1) -h -k -l2 //
| #G #L #K #V #i #l1 #HLK #_ #IHV #l2 #H
  elim (da_inv_lref … H) -H * #K0 #V0 [| #l0 ] #HLK0 #HV0 [| #Hl0 ]
  lapply (drop_mono … HLK0 … HLK) -HLK -HLK0 #H destruct /2 width=1/
| #G #L #K #W #i #l1 #HLK #_ #IHW #l2 #H
  elim (da_inv_lref … H) -H * #K0 #W0 [| #l0 ] #HLK0 #HW0 [| #Hl0 ]
  lapply (drop_mono … HLK0 … HLK) -HLK -HLK0 #H destruct /3 width=1/
| #a #I #G #L #V #T #l1 #_ #IHT #l2 #H
  lapply (da_inv_bind … H) -H /2 width=1/
| #I #G #L #V #T #l1 #_ #IHT #l2 #H
  lapply (da_inv_flat … H) -H /2 width=1/
]
qed-.
