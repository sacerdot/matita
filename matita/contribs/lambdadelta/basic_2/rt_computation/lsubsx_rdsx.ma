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

include "basic_2/rt_computation/rdsx_drops.ma".
include "basic_2/rt_computation/rdsx_lpxs.ma".
include "basic_2/rt_computation/lsubsx.ma".

(* CLEAR OF STRONGLY NORMALIZING ENTRIES FOR UNBOUND RT-TRANSITION **********)

(* Properties with strongly normalizing referred local environments *********)

(* Basic_2A1: uses: lsx_cpx_trans_lcosx *)
lemma rdsx_cpx_trans_lsubsx (h):
      ∀G,L0,T1,T2. ⦃G,L0⦄ ⊢ T1 ⬈[h] T2 →
      ∀f,L. G ⊢ L0 ⊆ⓧ[h,f] L →
      G ⊢ ⬈*[h,T1] 𝐒⦃L⦄ → G ⊢ ⬈*[h,T2] 𝐒⦃L⦄.
#h #G #L0 #T1 #T2 #H @(cpx_ind … H) -G -L0 -T1 -T2 //
[ #I0 #G #K0 #V1 #V2 #W2 #_ #IH #HVW2 #g #L #HK0 #HL
  elim (lsubsx_inv_pair_sn_gen … HK0) -HK0 *
  [ #f #K #HK0 #H1 #H2 destruct
    /4 width=8 by rdsx_lifts, rdsx_fwd_pair, drops_refl, drops_drop/
  | #f #K #HV1 #HK0 #H1 #H2 destruct
    /4 width=8 by rdsx_lifts, drops_refl, drops_drop/
  ]
| #I0 #G #K0 #T #U #i #_ #IH #HTU #g #L #HK0 #HL
  elim (lsubsx_fwd_bind_sn … HK0) -HK0 #I #K #HK0 #H destruct
  /6 width=8 by rdsx_inv_lifts, rdsx_lifts, drops_refl, drops_drop/
| #p #I0 #G #L0 #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #f #L #HL0 #HL
  elim (rdsx_inv_bind … HL) -HL
  /4 width=2 by lsubsx_pair, rdsx_bind_void/
| #I0 #G #L0 #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #f #L #HL0 #HL
  elim (rdsx_inv_flat … HL) -HL /3 width=2 by rdsx_flat/
| #G #L0 #V #U1 #T1 #T2 #HTU1 #_ #IHT12 #f #L #HL0 #HL
  elim (rdsx_inv_bind … HL) -HL #HV #HU1
  /5 width=8 by rdsx_inv_lifts, drops_refl, drops_drop/
| #G #L0 #V #T1 #T2 #_ #IHT12 #f #L #HL0 #HL
  elim (rdsx_inv_flat … HL) -HL /2 width=2 by/
| #G #L0 #V1 #V2 #T #_ #IHV12 #f #L #HL0 #HL
  elim (rdsx_inv_flat … HL) -HL /2 width=2 by/
| #p #G #L0 #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #IHV12 #IHW12 #IHT12 #f #L #HL0 #HL
  elim (rdsx_inv_flat … HL) -HL #HV1 #HL
  elim (rdsx_inv_bind … HL) -HL #HW1 #HT1
  /4 width=2 by lsubsx_pair, rdsx_bind_void, rdsx_flat/
| #p #G #L0 #V1 #V2 #U2 #W1 #W2 #T1 #T2 #_ #_ #_ #IHV12 #IHW12 #IHT12 #HVU2 #f #L #HL0 #HL
  elim (rdsx_inv_flat … HL) -HL #HV1 #HL
  elim (rdsx_inv_bind … HL) -HL #HW1 #HT1
  /6 width=8 by lsubsx_pair, rdsx_lifts, rdsx_bind_void, rdsx_flat, drops_refl, drops_drop/
]
qed-.

(* Advanced properties of strongly normalizing referred local environments **)

(* Basic_2A1: uses: lsx_cpx_trans_O *)
lemma rdsx_cpx_trans (h):
      ∀G,L,T1,T2. ⦃G,L⦄ ⊢ T1 ⬈[h] T2 →
      G ⊢ ⬈*[h,T1] 𝐒⦃L⦄ → G ⊢ ⬈*[h,T2] 𝐒⦃L⦄.
/3 width=6 by rdsx_cpx_trans_lsubsx, lsubsx_refl/ qed-.

lemma rdsx_cpxs_trans (h):
      ∀G,L,T1,T2. ⦃G,L⦄ ⊢ T1 ⬈*[h] T2 →
      G ⊢ ⬈*[h,T1] 𝐒⦃L⦄ → G ⊢ ⬈*[h,T2] 𝐒⦃L⦄.
#h #G #L #T1 #T2 #H
@(cpxs_ind_dx ???????? H) -T1 //
/3 width=3 by rdsx_cpx_trans/
qed-.
