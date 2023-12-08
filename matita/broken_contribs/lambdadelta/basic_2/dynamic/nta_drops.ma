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

include "basic_2/dynamic/cnv_drops.ma".
include "basic_2/dynamic/nta.ma".

(* NATIVE TYPE ASSIGNMENT FOR TERMS *****************************************)

(* Advanced properties ******************************************************)

lemma nta_ldef (h) (a) (G) (K):
      ∀V,W. ❨G,K❩ ⊢ V :[h,a] W →
      ∀U. ⇧[1] W ≘ U → ❨G,K.ⓓV❩ ⊢ #0 :[h,a] U.
#h #a #G #K #V #W #H #U #HWU
elim (cnv_inv_cast … H) -H #X #HW #HV #HWX #HVX
lapply (cnv_lifts … HW (ⓣ) … (K.ⓓV) … HWU) -HW
[ /3 width=3 by drops_refl, drops_drop/ ] #HU
elim (cpms_lifts_sn … HWX … (ⓣ) … (K.ⓓV) … HWU) -W
[| /3 width=3 by drops_refl, drops_drop/ ] #XW #HXW #HUXW
/3 width=5 by cnv_zero, cnv_cast, cpms_delta/
qed.

lemma nta_ldec_cnv (h) (a) (G) (K):
      ∀W. ❨G,K❩ ⊢ W ![h,a] →
      ∀U. ⇧[1] W ≘ U → ❨G,K.ⓛW❩ ⊢ #0 :[h,a] U.
#h #a #G #K #W #HW #U #HWU
lapply (cnv_lifts … HW (ⓣ) … (K.ⓛW) … HWU)
/3 width=5 by cnv_zero, cnv_cast, cpms_ell, drops_refl, drops_drop/
qed.

lemma nta_lref (h) (a) (I) (G) (K):
      ∀T,i. ❨G,K❩ ⊢ #i :[h,a] T →
      ∀U. ⇧[1] T ≘ U → ❨G,K.ⓘ[I]❩ ⊢ #(↑i) :[h,a] U.
#h #a #I #G #K #T #i #H #U #HTU
elim (cnv_inv_cast … H) -H #X #HT #Hi #HTX #H2
lapply (cnv_lifts … HT (ⓣ) … (K.ⓘ[I]) … HTU) -HT
[ /3 width=3 by drops_refl, drops_drop/ ] #HU
lapply (cnv_lifts … Hi (ⓣ) (𝐔❨1❩) (K.ⓘ[I]) ???) -Hi
[4:|*: /3 width=3 by drops_refl, drops_drop/ ] #Hi
elim (cpms_lifts_sn … HTX … (ⓣ) … (K.ⓘ[I]) … HTU) -T
[| /3 width=3 by drops_refl, drops_drop/ ] #XU #HXU #HUXU
/3 width=5 by cnv_cast, cpms_lref/
qed.

(* Properties with generic slicing for local environments *******************)

lemma nta_lifts_sn (h) (a) (G): d_liftable2_sn … lifts (nta a h G).
#h #a #G #K #T1 #T2 #H #b #f #L #HLK #U1 #HTU1
elim (cnv_inv_cast … H) -H #X #HT2 #HT1 #HT2X #HT1X
elim (lifts_total T2 f) #U2 #HTU2
lapply (cnv_lifts … HT2 … HLK … HTU2) -HT2 #HU2
lapply (cnv_lifts … HT1 … HLK … HTU1) -HT1 #HU1
elim (cpms_lifts_sn … HT2X … HLK … HTU2) -HT2X #X2 #HX2 #HUX2
elim (cpms_lifts_sn … HT1X … HLK … HTU1) -T1 #X1 #HX1 #HUX1
lapply (lifts_mono … HX2 … HX1) -K -X #H destruct
/3 width=6 by cnv_cast, ex2_intro/
qed-.

(* Basic_1: was: ty3_lift *)
(* Basic_2A1: was: nta_lift ntaa_lift *)
lemma nta_lifts_bi (h) (a) (G): d_liftable2_bi … lifts (nta a h G).
/3 width=12 by nta_lifts_sn, d_liftable2_sn_bi, lifts_mono/ qed-.

(* Basic_1: was by definition: ty3_abbr *)
(* Basic_2A1: was by definition: nta_ldef ntaa_ldef *)
lemma nta_ldef_drops (h) (a) (G) (K) (L) (i):
      ∀V,W. ❨G,K❩ ⊢ V :[h,a] W →
      ∀U. ⇧[↑i] W ≘ U → ⇩[i] L ≘ K.ⓓV → ❨G,L❩ ⊢ #i :[h,a] U.
#h #a #G #K #L #i #V #W #HVW #U #HWU #HLK
elim (lifts_split_trans … HWU (𝐔❨1❩) (𝐔❨i❩)) [| // ] #X #HWX #HXU
/3 width=9 by nta_lifts_bi, nta_ldef/
qed.

lemma nta_ldec_drops_cnv (h) (a) (G) (K) (L) (i):
      ∀W. ❨G,K❩ ⊢ W ![h,a] →
      ∀U. ⇧[↑i] W ≘ U → ⇩[i] L ≘ K.ⓛW → ❨G,L❩ ⊢ #i :[h,a] U.
#h #a #G #K #L #i #W #HW #U #HWU #HLK
elim (lifts_split_trans … HWU (𝐔❨1❩) (𝐔❨i❩)) [| // ] #X #HWX #HXU
/3 width=9 by nta_lifts_bi, nta_ldec_cnv/
qed.
