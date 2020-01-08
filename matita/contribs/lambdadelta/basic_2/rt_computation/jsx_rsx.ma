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

include "basic_2/rt_computation/rsx_drops.ma".
include "basic_2/rt_computation/rsx_lpxs.ma".
include "basic_2/rt_computation/jsx.ma".

(* COMPATIBILITY OF STRONG NORMALIZATION FOR UNBOUND RT-TRANSITION **********)

(* Properties with strongly normalizing referred local environments *********)

(* Basic_2A1: uses: lsx_cpx_trans_lcosx *)
lemma rsx_cpx_trans_jsx (h) (G):
      ∀L0,T1,T2. ❪G,L0❫ ⊢ T1 ⬈[h] T2 →
      ∀L. G ⊢ L0 ⊒[h] L → G ⊢ ⬈*[h,T1] 𝐒❪L❫ → G ⊢ ⬈*[h,T2] 𝐒❪L❫.
#h #G #L0 #T1 #T2 #H @(cpx_ind … H) -G -L0 -T1 -T2
[ //
| //
| #I0 #G #K0 #V1 #V2 #W2 #_ #IH #HVW2 #L #HK0 #HL
  elim (jsx_inv_pair_sn … HK0) -HK0 *
  [ #K #HK0 #H destruct
    /4 width=8 by rsx_lifts, rsx_fwd_pair, drops_refl, drops_drop/
  | #K #HK0 #HV1 #H destruct
    /4 width=8 by rsx_lifts, drops_refl, drops_drop/
  ]
| #I0 #G #K0 #T #U #i #_ #IH #HTU #L #HK0 #HL
  elim (jsx_fwd_bind_sn … HK0) -HK0 #I #K #HK0 #H destruct
  /6 width=8 by rsx_inv_lifts, rsx_lifts, drops_refl, drops_drop/
| #p #I0 #G #L0 #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #L #HL0 #HL
  elim (rsx_inv_bind_void … HL) -HL
  /4 width=2 by jsx_pair, rsx_bind_void/
| #I0 #G #L0 #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #L #HL0 #HL
  elim (rsx_inv_flat … HL) -HL /3 width=2 by rsx_flat/
| #G #L0 #V #U1 #T1 #T2 #HTU1 #_ #IHT12 #L #HL0 #HL
  elim (rsx_inv_bind_void … HL) -HL #HV #HU1
  /5 width=8 by rsx_inv_lifts, drops_refl, drops_drop/
| #G #L0 #V #T1 #T2 #_ #IHT12 #L #HL0 #HL
  elim (rsx_inv_flat … HL) -HL /2 width=2 by/
| #G #L0 #V1 #V2 #T #_ #IHV12 #L #HL0 #HL
  elim (rsx_inv_flat … HL) -HL /2 width=2 by/
| #p #G #L0 #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #IHV12 #IHW12 #IHT12 #L #HL0 #HL
  elim (rsx_inv_flat … HL) -HL #HV1 #HL
  elim (rsx_inv_bind_void … HL) -HL #HW1 #HT1
  /4 width=2 by jsx_pair, rsx_bind_void, rsx_flat/
| #p #G #L0 #V1 #V2 #U2 #W1 #W2 #T1 #T2 #_ #_ #_ #IHV12 #IHW12 #IHT12 #HVU2 #L #HL0 #HL
  elim (rsx_inv_flat … HL) -HL #HV1 #HL
  elim (rsx_inv_bind_void … HL) -HL #HW1 #HT1
  /6 width=8 by jsx_pair, rsx_lifts, rsx_bind_void, rsx_flat, drops_refl, drops_drop/
]
qed-.

(* Advanced properties of strongly normalizing referred local environments **)

(* Basic_2A1: uses: lsx_cpx_trans_O *)
lemma rsx_cpx_trans (h) (G):
      ∀L,T1,T2. ❪G,L❫ ⊢ T1 ⬈[h] T2 →
      G ⊢ ⬈*[h,T1] 𝐒❪L❫ → G ⊢ ⬈*[h,T2] 𝐒❪L❫.
/3 width=6 by rsx_cpx_trans_jsx, jsx_refl/ qed-.

lemma rsx_cpxs_trans (h) (G):
      ∀L,T1,T2. ❪G,L❫ ⊢ T1 ⬈*[h] T2 →
      G ⊢ ⬈*[h,T1] 𝐒❪L❫ → G ⊢ ⬈*[h,T2] 𝐒❪L❫.
#h #G #L #T1 #T2 #H
@(cpxs_ind_dx ???????? H) -T1 //
/3 width=3 by rsx_cpx_trans/
qed-.
