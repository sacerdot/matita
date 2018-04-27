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

include "basic_2/rt_computation/lfsx_drops.ma".
include "basic_2/rt_computation/lfsx_lfpxs.ma".
include "basic_2/rt_computation/lsubsx.ma".

(* CLEAR OF STRONGLY NORMALIZING ENTRIES FOR UNBOUND RT-TRANSITION **********)

(* Properties with strong normalizing env's for unbound rt-transition *******)

(* Basic_2A1: uses: lsx_cpx_trans_lcosx *)
lemma lfsx_cpx_trans_lsubsx: ∀h,o,G,L0,T1,T2. ⦃G, L0⦄ ⊢ T1 ⬈[h] T2 →
                             ∀f,L. G ⊢ L0 ⊆ⓧ[h, o, f] L →
                             G ⊢ ⬈*[h, o, T1] 𝐒⦃L⦄ → G ⊢ ⬈*[h, o, T2] 𝐒⦃L⦄.
#h #o #G #L0 #T1 #T2 #H @(cpx_ind … H) -G -L0 -T1 -T2 //
[ #I0 #G #K0 #V1 #V2 #W2 #_ #IH #HVW2 #g #L #HK0 #HL
  elim (lsubsx_inv_pair_sn_gen … HK0) -HK0 *
  [ #f #K #HK0 #H1 #H2 destruct
    /4 width=8 by lfsx_lifts, lfsx_fwd_pair, drops_refl, drops_drop/
  | #f #K #HV1 #HK0 #H1 #H2 destruct
    /4 width=8 by lfsx_lifts, drops_refl, drops_drop/
  ]
| #I0 #G #K0 #T #U #i #_ #IH #HTU #g #L #HK0 #HL
  elim (lsubsx_fwd_bind_sn … HK0) -HK0 #I #K #HK0 #H destruct
  /6 width=8 by lfsx_inv_lifts, lfsx_lifts, drops_refl, drops_drop/
| #p #I0 #G #L0 #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #f #L #HL0 #HL
  elim (lfsx_inv_bind … HL) -HL
  /4 width=2 by lsubsx_pair, lfsx_bind_void/
| #I0 #G #L0 #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #f #L #HL0 #HL
  elim (lfsx_inv_flat … HL) -HL /3 width=2 by lfsx_flat/
| #G #L0 #V #U1 #U2 #T2 #_ #HTU2 #IHU12 #f #L #HL0 #HL
  elim (lfsx_inv_bind … HL) -HL #HV #HU1
  /4 width=8 by lsubsx_pair, lfsx_inv_lifts, drops_refl, drops_drop/
| #G #L0 #V #T1 #T2 #_ #IHT12 #f #L #HL0 #HL
  elim (lfsx_inv_flat … HL) -HL /2 width=2 by/
| #G #L0 #V1 #V2 #T #_ #IHV12 #f #L #HL0 #HL
  elim (lfsx_inv_flat … HL) -HL /2 width=2 by/
| #p #G #L0 #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #IHV12 #IHW12 #IHT12 #f #L #HL0 #HL
  elim (lfsx_inv_flat … HL) -HL #HV1 #HL
  elim (lfsx_inv_bind … HL) -HL #HW1 #HT1
  /4 width=2 by lsubsx_pair, lfsx_bind_void, lfsx_flat/
| #p #G #L0 #V1 #V2 #U2 #W1 #W2 #T1 #T2 #_ #_ #_ #IHV12 #IHW12 #IHT12 #HVU2 #f #L #HL0 #HL
  elim (lfsx_inv_flat … HL) -HL #HV1 #HL
  elim (lfsx_inv_bind … HL) -HL #HW1 #HT1
  /6 width=8 by lsubsx_pair, lfsx_lifts, lfsx_bind_void, lfsx_flat, drops_refl, drops_drop/
]
qed-.

(* Basic_2A1: uses: lsx_cpx_trans_O *)
lemma lfsx_cpx_trans: ∀h,o,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ⬈[h] T2 →
                      G ⊢ ⬈*[h, o, T1] 𝐒⦃L⦄ → G ⊢ ⬈*[h, o, T2] 𝐒⦃L⦄.
/3 width=6 by lfsx_cpx_trans_lsubsx, lsubsx_refl/ qed-.

(* Properties with strong normalizing env's for unbound rt-computation ******)

lemma lfsx_cpxs_trans: ∀h,o,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ⬈*[h] T2 →
                       G ⊢ ⬈*[h, o, T1] 𝐒⦃L⦄ → G ⊢ ⬈*[h, o, T2] 𝐒⦃L⦄.
#h #o #G #L #T1 #T2 #H
@(cpxs_ind_dx ???????? H) -T1 //
/3 width=3 by lfsx_cpx_trans/
qed-.
