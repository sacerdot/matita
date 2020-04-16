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

include "ground/xoa/ex_5_1.ma".
include "ground/xoa/ex_8_5.ma".
include "ground/xoa/ex_9_3.ma".
include "basic_2/rt_transition/cpm_teqx.ma".
include "basic_2/rt_computation/fpbg_fqup.ma".
include "basic_2/dynamic/cnv_fsb.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

(* Inversion lemmas with restricted rt-transition for terms *****************)

lemma cnv_cpr_teqx_fwd_refl (h) (a) (G) (L):
      ∀T1,T2. ❪G,L❫ ⊢ T1 ➡[h,0] T2 → T1 ≛ T2 → ❪G,L❫ ⊢ T1 ![h,a] → T1 = T2.
#h #a #G #L #T1 #T2 #H @(cpr_ind … H) -G -L -T1 -T2
[ //
| #G #K #V1 #V2 #X2 #_ #_ #_ #H1 #_ -a -G -K -V1 -V2
  lapply (teqx_inv_lref1 … H1) -H1 #H destruct //
| #I #G #K #T2 #X2 #i #_ #_ #_ #H1 #_ -a -I -G -K -T2
  lapply (teqx_inv_lref1 … H1) -H1 #H destruct //
| #p #I #G #L #V1 #V2 #T1 #T2 #_ #_ #IHV #IHT #H1 #H2
  elim (teqx_inv_pair1 … H1) -H1 #V0 #T0 #HV0 #HT0 #H destruct
  elim (cnv_inv_bind … H2) -H2 #HV1 #HT1
  /3 width=3 by eq_f2/
| #I #G #L #V1 #V2 #T1 #T2 #_ #_ #IHV #IHT #H1 #H2
  elim (teqx_inv_pair1 … H1) -H1 #V0 #T0 #HV0 #HT0 #H destruct
  elim (cnv_fwd_flat … H2) -H2 #HV1 #HT1
  /3 width=3 by eq_f2/
| #G #K #V #T1 #X1 #X2 #HXT1 #HX12 #_ #H1 #H2
  elim (cnv_fpbg_refl_false … H2) -a
  @(fpbg_teqx_div … H1) -H1
  /3 width=9 by cpm_tneqx_cpm_fpbg, cpm_zeta, teqx_lifts_inv_pair_sn/
| #G #L #U #T1 #T2 #HT12 #_ #H1 #H2
  elim (cnv_fpbg_refl_false … H2) -a
  @(fpbg_teqx_div … H1) -H1
  /3 width=7 by cpm_tneqx_cpm_fpbg, cpm_eps, teqx_inv_pair_xy_y/
| #p #G #L #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #_ #_ #H1 #_
  elim (teqx_inv_pair … H1) -H1 #H #_ #_ destruct
| #p #G #L #V1 #V2 #X2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #_ #_ #_ #H1 #_
  elim (teqx_inv_pair … H1) -H1 #H #_ #_ destruct
]
qed-.

lemma cpm_teqx_inv_bind_sn (h) (a) (n) (p) (I) (G) (L):
      ∀V,T1. ❪G,L❫ ⊢ ⓑ[p,I]V.T1 ![h,a] →
      ∀X. ❪G,L❫ ⊢ ⓑ[p,I]V.T1 ➡[h,n] X → ⓑ[p,I]V.T1 ≛ X →
      ∃∃T2. ❪G,L❫ ⊢ V ![h,a] & ❪G,L.ⓑ[I]V❫ ⊢ T1 ![h,a] & ❪G,L.ⓑ[I]V❫ ⊢ T1 ➡[h,n] T2 & T1 ≛ T2 & X = ⓑ[p,I]V.T2.
#h #a #n #p #I #G #L #V #T1 #H0 #X #H1 #H2
elim (cpm_inv_bind1 … H1) -H1 *
[ #XV #T2 #HXV #HT12 #H destruct
  elim (teqx_inv_pair … H2) -H2 #_ #H2XV #H2T12
  elim (cnv_inv_bind … H0) -H0 #HV #HT
  lapply (cnv_cpr_teqx_fwd_refl … HXV H2XV HV) #H destruct -HXV -H2XV
  /2 width=4 by ex5_intro/
| #X1 #HXT1 #HX1 #H1 #H destruct
  elim (cnv_fpbg_refl_false … H0) -a
  @(fpbg_teqx_div … H2) -H2
  /3 width=9 by cpm_tneqx_cpm_fpbg, cpm_zeta, teqx_lifts_inv_pair_sn/
]
qed-.

lemma cpm_teqx_inv_appl_sn (h) (a) (n) (G) (L):
      ∀V,T1. ❪G,L❫ ⊢ ⓐV.T1 ![h,a] →
      ∀X. ❪G,L❫ ⊢ ⓐV.T1 ➡[h,n] X → ⓐV.T1 ≛ X →
      ∃∃m,q,W,U1,T2. ad a m & ❪G,L❫ ⊢ V ![h,a] & ❪G,L❫ ⊢ V ➡*[h,1] W & ❪G,L❫ ⊢ T1 ➡*[h,m] ⓛ[q]W.U1
                   & ❪G,L❫⊢ T1 ![h,a] & ❪G,L❫ ⊢ T1 ➡[h,n] T2 & T1 ≛ T2 & X = ⓐV.T2.
#h #a #n #G #L #V #T1 #H0 #X #H1 #H2
elim (cpm_inv_appl1 … H1) -H1 *
[ #XV #T2 #HXV #HT12 #H destruct
  elim (teqx_inv_pair … H2) -H2 #_ #H2XV #H2T12
  elim (cnv_inv_appl … H0) -H0 #m #q #W #U1 #Hm #HV #HT #HVW #HTU1
  lapply (cnv_cpr_teqx_fwd_refl … HXV H2XV HV) #H destruct -HXV -H2XV
  /3 width=7 by ex8_5_intro/
| #q #V2 #W1 #W2 #XT #T2 #_ #_ #_ #H1 #H destruct -H0
  elim (teqx_inv_pair … H2) -H2 #H #_ #_ destruct
| #q #V2 #XV #W1 #W2 #XT #T2 #_ #_ #_ #_ #H1 #H destruct -H0
  elim (teqx_inv_pair … H2) -H2 #H #_ #_ destruct
]
qed-.

lemma cpm_teqx_inv_cast_sn (h) (a) (n) (G) (L):
      ∀U1,T1. ❪G,L❫ ⊢ ⓝU1.T1 ![h,a] →
      ∀X. ❪G,L❫ ⊢ ⓝU1.T1 ➡[h,n] X → ⓝU1.T1 ≛ X →
      ∃∃U0,U2,T2. ❪G,L❫ ⊢ U1 ➡*[h,0] U0 & ❪G,L❫ ⊢ T1 ➡*[h,1] U0
                & ❪G,L❫ ⊢ U1 ![h,a] & ❪G,L❫ ⊢ U1 ➡[h,n] U2 & U1 ≛ U2
                & ❪G,L❫ ⊢ T1 ![h,a] & ❪G,L❫ ⊢ T1 ➡[h,n] T2 & T1 ≛ T2 & X = ⓝU2.T2.
#h #a #n #G #L #U1 #T1 #H0 #X #H1 #H2
elim (cpm_inv_cast1 … H1) -H1 [ * || * ]
[ #U2 #T2 #HU12 #HT12 #H destruct
  elim (teqx_inv_pair … H2) -H2 #_ #H2U12 #H2T12
  elim (cnv_inv_cast … H0) -H0 #U0 #HU1 #HT1 #HU10 #HT1U0
  /2 width=7 by ex9_3_intro/
| #HT1X
  elim (cnv_fpbg_refl_false … H0) -a
  @(fpbg_teqx_div … H2) -H2
  /3 width=7 by cpm_tneqx_cpm_fpbg, cpm_eps, teqx_inv_pair_xy_y/
| #m #HU1X #H destruct
  elim (cnv_fpbg_refl_false … H0) -a
  @(fpbg_teqx_div … H2) -H2
  /3 width=7 by cpm_tneqx_cpm_fpbg, cpm_ee, teqx_inv_pair_xy_x/
]
qed-.

lemma cpm_teqx_inv_bind_dx (h) (a) (n) (p) (I) (G) (L):
      ∀X. ❪G,L❫ ⊢ X ![h,a] →
      ∀V,T2. ❪G,L❫ ⊢ X ➡[h,n] ⓑ[p,I]V.T2 → X ≛ ⓑ[p,I]V.T2 →
      ∃∃T1. ❪G,L❫ ⊢ V ![h,a] & ❪G,L.ⓑ[I]V❫ ⊢ T1 ![h,a] & ❪G,L.ⓑ[I]V❫ ⊢ T1 ➡[h,n] T2 & T1 ≛ T2 & X = ⓑ[p,I]V.T1.
#h #a #n #p #I #G #L #X #H0 #V #T2 #H1 #H2
elim (teqx_inv_pair2 … H2) #V0 #T1 #_ #_ #H destruct
elim (cpm_teqx_inv_bind_sn … H0 … H1 H2) -H0 -H1 -H2 #T0 #HV #HT1 #H1T12 #H2T12 #H destruct
/2 width=5 by ex5_intro/
qed-.

(* Eliminators with restricted rt-transition for terms **********************)

lemma cpm_teqx_ind (h) (a) (n) (G) (Q:relation3 …):
      (∀I,L. n = 0 → Q L (⓪[I]) (⓪[I])) →
      (∀L,s. n = 1 → Q L (⋆s) (⋆(⫯[h]s))) →
      (∀p,I,L,V,T1. ❪G,L❫⊢ V![h,a] → ❪G,L.ⓑ[I]V❫⊢T1![h,a] →
        ∀T2. ❪G,L.ⓑ[I]V❫ ⊢ T1 ➡[h,n] T2 → T1 ≛ T2 →
        Q (L.ⓑ[I]V) T1 T2 → Q L (ⓑ[p,I]V.T1) (ⓑ[p,I]V.T2)
      ) →
      (∀m. ad a m →
        ∀L,V. ❪G,L❫ ⊢ V ![h,a] → ∀W. ❪G,L❫ ⊢ V ➡*[h,1] W →
        ∀p,T1,U1. ❪G,L❫ ⊢ T1 ➡*[h,m] ⓛ[p]W.U1 → ❪G,L❫⊢ T1 ![h,a] →
        ∀T2. ❪G,L❫ ⊢ T1 ➡[h,n] T2 → T1 ≛ T2 →
        Q L T1 T2 → Q L (ⓐV.T1) (ⓐV.T2)
      ) →
      (∀L,U0,U1,T1. ❪G,L❫ ⊢ U1 ➡*[h,0] U0 → ❪G,L❫ ⊢ T1 ➡*[h,1] U0 →
        ∀U2. ❪G,L❫ ⊢ U1 ![h,a] → ❪G,L❫ ⊢ U1 ➡[h,n] U2 → U1 ≛ U2 →
        ∀T2. ❪G,L❫ ⊢ T1 ![h,a] → ❪G,L❫ ⊢ T1 ➡[h,n] T2 → T1 ≛ T2 →
        Q L U1 U2 → Q L T1 T2 → Q L (ⓝU1.T1) (ⓝU2.T2)
      ) →
      ∀L,T1. ❪G,L❫ ⊢ T1 ![h,a] →
      ∀T2. ❪G,L❫ ⊢ T1 ➡[h,n] T2 → T1 ≛ T2 → Q L T1 T2.
#h #a #n #G #Q #IH1 #IH2 #IH3 #IH4 #IH5 #L #T1
@(insert_eq_0 … G) #F
@(fqup_wf_ind_eq (Ⓣ) … F L T1) -L -T1 -F
#G0 #L0 #T0 #IH #F #L * [| * [| * ]]
[ #I #_ #_ #_ #_ #HF #X #H1X #H2X destruct -G0 -L0 -T0
  elim (cpm_teqx_inv_atom_sn … H1X H2X) -H1X -H2X *
  [ #H1 #H2 destruct /2 width=1 by/
  | #s #H1 #H2 #H3 destruct /2 width=1 by/
  ]
| #p #I #V #T1 #HG #HL #HT #H0 #HF #X #H1X #H2X destruct
  elim (cpm_teqx_inv_bind_sn … H0 … H1X H2X) -H0 -H1X -H2X #T2 #HV #HT1 #H1T12 #H2T12 #H destruct
  /3 width=5 by/
| #V #T1 #HG #HL #HT #H0 #HF #X #H1X #H2X destruct
  elim (cpm_teqx_inv_appl_sn … H0 … H1X H2X) -H0 -H1X -H2X #m #q #W #U1 #T2 #Hm #HV #HVW #HTU1 #HT1 #H1T12 #H2T12 #H destruct
  /3 width=7 by/
| #U1 #T1 #HG #HL #HT #H0 #HF #X #H1X #H2X destruct
  elim (cpm_teqx_inv_cast_sn … H0 … H1X H2X) -H0 -H1X -H2X #U0 #U2 #T2 #HU10 #HT1U0 #HU1 #H1U12 #H2U12 #HT1 #H1T12 #H2T12 #H destruct
  /3 width=5 by/
]
qed-.

(* Advanced properties with restricted rt-transition for terms **************)

lemma cpm_teqx_free (h) (a) (n) (G) (L):
      ∀T1. ❪G,L❫ ⊢ T1 ![h,a] →
      ∀T2. ❪G,L❫ ⊢ T1 ➡[h,n] T2 → T1 ≛ T2 →
      ∀F,K. ❪F,K❫ ⊢ T1 ➡[h,n] T2.
#h #a #n #G #L #T1 #H0 #T2 #H1 #H2
@(cpm_teqx_ind … H0 … H1 H2) -L -T1 -T2
[ #I #L #H #F #K destruct //
| #L #s #H #F #K destruct //
| #p #I #L #V #T1 #_ #_ #T2 #_ #_ #IH #F #K
  /2 width=1 by cpm_bind/
| #m #_ #L #V #_ #W #_ #q #T1 #U1 #_ #_ #T2 #_ #_ #IH #F #K
  /2 width=1 by cpm_appl/
| #L #U0 #U1 #T1 #_ #_ #U2 #_ #_ #_ #T2 #_ #_ #_ #IHU #IHT #F #K
  /2 width=1 by cpm_cast/
]
qed-.

(* Advanced inversion lemmas with restricted rt-transition for terms ********)

lemma cpm_teqx_inv_bind_sn_void (h) (a) (n) (p) (I) (G) (L):
      ∀V,T1. ❪G,L❫ ⊢ ⓑ[p,I]V.T1 ![h,a] →
      ∀X. ❪G,L❫ ⊢ ⓑ[p,I]V.T1 ➡[h,n] X → ⓑ[p,I]V.T1 ≛ X →
      ∃∃T2. ❪G,L❫ ⊢ V ![h,a] & ❪G,L.ⓑ[I]V❫ ⊢ T1 ![h,a] & ❪G,L.ⓧ❫ ⊢ T1 ➡[h,n] T2 & T1 ≛ T2 & X = ⓑ[p,I]V.T2.
#h #a #n #p #I #G #L #V #T1 #H0 #X #H1 #H2
elim (cpm_teqx_inv_bind_sn … H0 … H1 H2) -H0 -H1 -H2 #T2 #HV #HT1 #H1T12 #H2T12 #H
/3 width=5 by ex5_intro, cpm_teqx_free/
qed-.
