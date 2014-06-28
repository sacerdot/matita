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

include "ground_2/ynat/ynat_max.ma".
include "basic_2/computation/lsx_drop.ma".
include "basic_2/computation/lsx_lpx.ma".
include "basic_2/computation/lsx_lpxs.ma".
include "basic_2/computation/lcosx.ma".

(* SN EXTENDED STRONGLY CONORMALIZING LOCAL ENVIRONMENTS ********************)

(* Properties on extended context-sensitive parallel reduction for term *****)

lemma lsx_cpx_trans_lcosx: ∀h,g,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡[h, g] T2 →
                           ∀d. G ⊢ ~⬊*[h, g, d] L →
                           G ⊢ ⬊*[h, g, T1, d] L → G ⊢ ⬊*[h, g, T2, d] L.
#h #g #G #L #T1 #T2 #H elim H -G -L -T1 -T2 //
[ #I #G #L #K #V1 #V2 #W2 #i #HLK #_ #HVW2 #IHV12 #d #HL #H
  elim (ylt_split i d) #Hdi [ -H | -HL ]
  [ <(ymax_pre_sn d (⫯i)) /2 width=1 by ylt_fwd_le_succ/
    elim (lcosx_drop_trans_lt … HL … HLK) // -HL -Hdi
    lapply (drop_fwd_drop2 … HLK) -HLK /3 width=7 by lsx_lift_ge/
  | lapply (lsx_fwd_lref_be … H … HLK) // -H -Hdi
    lapply (drop_fwd_drop2 … HLK) -HLK
    /4 width=10 by lsx_ge, lsx_lift_le/
  ]
| #a #I #G #L #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #d #HL #H
  elim (lsx_inv_bind … H) -H #HV1 #HT1
  @lsx_bind /2 width=2 by/ (**) (* explicit constructor *)
  @(lsx_leq_conf … (L.ⓑ{I}V1)) /3 width=1 by lcosx_pair, leq_succ/
| #I #G #L #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #d #HL #H
  elim (lsx_inv_flat … H) -H /3 width=1 by lsx_flat/
| #G #L #V #U1 #U2 #T2 #_ #HTU2 #IHU12 #d #HL #H
  elim (lsx_inv_bind … H) -H
  /4 width=9 by lcosx_pair, lsx_inv_lift_ge, drop_drop/
| #G #L #V #T1 #T2 #_ #IHT12 #d #HL #H
  elim (lsx_inv_flat … H) -H /2 width=1 by/
| #G #L #V1 #V2 #T #_ #IHV12 #d #HL #H
  elim (lsx_inv_flat … H) -H /2 width=1 by/
| #a #G #L #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #IHV12 #IHW12 #IHT12 #d #HL #H
  elim (lsx_inv_flat … H) -H #HV1 #H
  elim (lsx_inv_bind … H) -H #HW1 #HT1
  @lsx_bind /3 width=1 by lsx_flat/ (**) (* explicit constructor *)
  @(lsx_leq_conf … (L.ⓛW1)) /3 width=1 by lcosx_pair, leq_succ/
| #a #G #L #V1 #V2 #U2 #W1 #W2 #T1 #T2 #_ #HVU2 #_ #_ #IHV12 #IHW12 #IHT12 #d #HL #H
  elim (lsx_inv_flat … H) -H #HV1 #H
  elim (lsx_inv_bind … H) -H #HW1 #HT1
  @lsx_bind /2 width=1 by/ (**) (* explicit constructor *)
  @lsx_flat [ /3 width=7 by lsx_lift_ge, drop_drop/ ]
  @(lsx_leq_conf … (L.ⓓW1)) /3 width=1 by lcosx_pair, leq_succ/
]
qed-.

lemma lsx_cpx_trans_O: ∀h,g,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡[h, g] T2 →
                       G ⊢ ⬊*[h, g, T1, 0] L → G ⊢ ⬊*[h, g, T2, 0] L.
/2 width=3 by lsx_cpx_trans_lcosx/ qed-.
