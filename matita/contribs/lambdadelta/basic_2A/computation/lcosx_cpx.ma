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

include "basic_2A/computation/lsx_drop.ma".
include "basic_2A/computation/lsx_lpx.ma".
include "basic_2A/computation/lsx_lpxs.ma".
include "basic_2A/computation/lcosx.ma".

(* SN EXTENDED STRONGLY CONORMALIZING LOCAL ENVIRONMENTS ********************)

(* Properties on extended context-sensitive parallel reduction for term *****)

lemma lsx_cpx_trans_lcosx: ∀h,g,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡[h, g] T2 →
                           ∀l. G ⊢ ~⬊*[h, g, l] L →
                           G ⊢ ⬊*[h, g, T1, l] L → G ⊢ ⬊*[h, g, T2, l] L.
#h #g #G #L #T1 #T2 #H elim H -G -L -T1 -T2 //
[ #I #G #L #K #V1 #V2 #W2 #i #HLK #_ #HVW2 #IHV12 #l #HL #H
  elim (ylt_split i l) #Hli [ -H | -HL ]
  [ elim (lcosx_drop_trans_lt … HL … HLK) // -HL
    <yminus_succ2 #H1K #H2K
    lapply (ylt_fwd_le_succ1 … Hli) -Hli #Hli
    >(yminus_plus l (↑i))
    /4 width=7 by lsx_lift_ge, drop_fwd_drop2/
  | lapply (lsx_fwd_lref_be … H … HLK) // -H -Hli
    lapply (drop_fwd_drop2 … HLK) -HLK
    /4 width=10 by lsx_ge, lsx_lift_le/
  ]
| #a #I #G #L #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #l #HL #H
  elim (lsx_inv_bind … H) -H #HV1 #HT1
  @lsx_bind /2 width=2 by/ (**) (* explicit constructor *)
  @(lsx_lreq_conf … (L.ⓑ{I}V1)) /3 width=1 by lcosx_pair, lreq_succ/
| #I #G #L #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #l #HL #H
  elim (lsx_inv_flat … H) -H /3 width=1 by lsx_flat/
| #G #L #V #U1 #U2 #T2 #_ #HTU2 #IHU12 #l #HL #H
  elim (lsx_inv_bind … H) -H #H1L #H2L <(yplus_minus l 1)
  /4 width=9 by lcosx_pair, lsx_inv_lift_ge, drop_drop/
| #G #L #V #T1 #T2 #_ #IHT12 #l #HL #H
  elim (lsx_inv_flat … H) -H /2 width=1 by/
| #G #L #V1 #V2 #T #_ #IHV12 #l #HL #H
  elim (lsx_inv_flat … H) -H /2 width=1 by/
| #a #G #L #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #IHV12 #IHW12 #IHT12 #l #HL #H
  elim (lsx_inv_flat … H) -H #HV1 #H
  elim (lsx_inv_bind … H) -H #HW1 #HT1
  @lsx_bind /3 width=1 by lsx_flat/ (**) (* explicit constructor *)
  @(lsx_lreq_conf … (L.ⓛW1)) /3 width=1 by lcosx_pair, lreq_succ/
| #a #G #L #V1 #V2 #U2 #W1 #W2 #T1 #T2 #_ #HVU2 #_ #_ #IHV12 #IHW12 #IHT12 #l #HL #H
  elim (lsx_inv_flat … H) -H #HV1 #H
  elim (lsx_inv_bind … H) -H #HW1 #HT1
  @lsx_bind /2 width=1 by/ (**) (* explicit constructor *)
  @lsx_flat [ <(yplus_SO2 l) /3 width=7 by lsx_lift_ge, drop_drop/ ]
  @(lsx_lreq_conf … (L.ⓓW1)) /3 width=1 by lcosx_pair, lreq_succ/
]
qed-.

lemma lsx_cpx_trans_O: ∀h,g,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡[h, g] T2 →
                       G ⊢ ⬊*[h, g, T1, 0] L → G ⊢ ⬊*[h, g, T2, 0] L.
/2 width=3 by lsx_cpx_trans_lcosx/ qed-.
