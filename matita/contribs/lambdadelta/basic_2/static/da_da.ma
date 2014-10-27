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

theorem da_mono: ∀h,g,G,L,T,d1. ⦃G, L⦄ ⊢ T ▪[h, g] d1 →
                 ∀d2. ⦃G, L⦄ ⊢ T ▪[h, g] d2 → d1 = d2.
#h #g #G #L #T #d1 #H elim H -G -L -T -d1
[ #G #L #k #d1 #Hkd1 #d2 #H
  lapply (da_inv_sort … H) -G -L #Hkd2
  >(deg_mono … Hkd2 … Hkd1) -h -k -d2 //
| #G #L #K #V #i #d1 #HLK #_ #IHV #d2 #H
  elim (da_inv_lref … H) -H * #K0 #V0 [| #d0 ] #HLK0 #HV0 [| #Hd0 ]
  lapply (drop_mono … HLK0 … HLK) -HLK -HLK0 #H destruct /2 width=1 by/
| #G #L #K #W #i #d1 #HLK #_ #IHW #d2 #H
  elim (da_inv_lref … H) -H * #K0 #W0 [| #d0 ] #HLK0 #HW0 [| #Hd0 ]
  lapply (drop_mono … HLK0 … HLK) -HLK -HLK0 #H destruct /3 width=1 by eq_f/
| #a #I #G #L #V #T #d1 #_ #IHT #d2 #H
  lapply (da_inv_bind … H) -H /2 width=1 by/
| #I #G #L #V #T #d1 #_ #IHT #d2 #H
  lapply (da_inv_flat … H) -H /2 width=1 by/
]
qed-.
