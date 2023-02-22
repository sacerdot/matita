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

include "basic_2A/static/da_da.ma".
include "basic_2A/static/lsubd.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR DEGREE ASSIGNMENT ***********************)

(* Properties on degree assignment ******************************************)

lemma lsubd_da_trans: ∀h,g,G,L2,T,d. ⦃G, L2⦄ ⊢ T ▪[h, g] d →
                      ∀L1. G ⊢ L1 ⫃▪[h, g] L2 → ⦃G, L1⦄ ⊢ T ▪[h, g] d.
#h #g #G #L2 #T #d #H elim H -G -L2 -T -d
[ /2 width=1 by da_sort/
| #G #L2 #K2 #V #i #d #HLK2 #_ #IHV #L1 #HL12
  elim (lsubd_drop_O1_trans … HL12 … HLK2) -L2 #X #H #HLK1
  elim (lsubd_inv_pair2 … H) -H * #K1 [ | -IHV -HLK1 ]
  [ #HK12 #H destruct /3 width=4 by da_ldef/
  | #W #d0 #_ #_ #_ #H destruct
  ]
| #G #L2 #K2 #W #i #d #HLK2 #HW #IHW #L1 #HL12
  elim (lsubd_drop_O1_trans … HL12 … HLK2) -L2 #X #H #HLK1
  elim (lsubd_inv_pair2 … H) -H * #K1 [ -HW | -IHW ]
  [ #HK12 #H destruct /3 width=4 by da_ldec/
  | #V #d0 #HV #H0W #_ #_ #H destruct
    lapply (da_mono … H0W … HW) -H0W -HW #H destruct /3 width=7 by da_ldef, da_flat/
  ]
| /4 width=1 by lsubd_pair, da_bind/
| /3 width=1 by da_flat/
]
qed-.

lemma lsubd_da_conf: ∀h,g,G,L1,T,d. ⦃G, L1⦄ ⊢ T ▪[h, g] d →
                     ∀L2. G ⊢ L1 ⫃▪[h, g] L2 → ⦃G, L2⦄ ⊢ T ▪[h, g] d.
#h #g #G #L1 #T #d #H elim H -G -L1 -T -d
[ /2 width=1 by da_sort/
| #G #L1 #K1 #V #i #d #HLK1 #HV #IHV #L2 #HL12
  elim (lsubd_drop_O1_conf … HL12 … HLK1) -L1 #X #H #HLK2
  elim (lsubd_inv_pair1 … H) -H * #K2 [ -HV | -IHV ]
  [ #HK12 #H destruct /3 width=4 by da_ldef/
  | #W0 #V0 #d0 #HV0 #HW0 #_ #_ #H1 #H2 destruct
    lapply (da_inv_flat … HV) -HV #H0V0
    lapply (da_mono … H0V0 … HV0) -H0V0 -HV0 #H destruct /2 width=4 by da_ldec/
  ]
| #G #L1 #K1 #W #i #d #HLK1 #HW #IHW #L2 #HL12
  elim (lsubd_drop_O1_conf … HL12 … HLK1) -L1 #X #H #HLK2
  elim (lsubd_inv_pair1 … H) -H * #K2 [ -HW | -IHW ]
  [ #HK12 #H destruct /3 width=4 by da_ldec/
  | #W0 #V0 #d0 #HV0 #HW0 #_ #H destruct
  ]
| /4 width=1 by lsubd_pair, da_bind/
| /3 width=1 by da_flat/
]
qed-.
