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

include "basic_2/grammar/tsts.ma".
include "basic_2/computation/lpxs_cpxs.ma".

(* CONTEXT-SENSITIVE EXTENDED PARALLEL COMPUTATION ON TERMS *****************)

(* Forward lemmas involving same top term structure *************************)

lemma cpxs_fwd_cnx: ∀h,g,G,L,T. ⦃G, L⦄ ⊢ ➡[h, g] 𝐍⦃T⦄ → ∀U. ⦃G, L⦄ ⊢ T ➡*[h, g] U → T ≂ U.
#h #g #G #L #T #HT #U #H
>(cpxs_inv_cnx1 … H HT) -G -L -T //
qed-.

lemma cpxs_fwd_sort: ∀h,g,G,L,U,k. ⦃G, L⦄ ⊢ ⋆k ➡*[h, g] U →
                     ⋆k ≂ U ∨ ⦃G, L⦄ ⊢ ⋆(next h k) ➡*[h, g] U.
#h #g #G #L #U #k #H
elim (cpxs_inv_sort1 … H) -H #n #l generalize in match k; -k @(nat_ind_plus … n) -n
[ #k #_ #H -l destruct /2 width=1 by or_introl/
| #n #IHn #k >plus_plus_comm_23 #Hnl #H destruct
  lapply (deg_next_SO … Hnl) -Hnl #Hnl
  elim (IHn … Hnl) -IHn
  [ #H lapply (tsts_inv_atom1 … H) -H #H >H -H /2 width=1 by or_intror/
  | generalize in match Hnl; -Hnl @(nat_ind_plus … n) -n
    /4 width=3 by cpxs_strap2, cpx_st, or_intror/
  | >iter_SO >iter_n_Sm //
  ]
]
qed-.

(* Basic_1: was just: pr3_iso_beta *)
lemma cpxs_fwd_beta: ∀h,g,a,G,L,V,W,T,U. ⦃G, L⦄ ⊢ ⓐV.ⓛ{a}W.T ➡*[h, g] U →
                     ⓐV.ⓛ{a}W.T ≂ U ∨ ⦃G, L⦄ ⊢ ⓓ{a}ⓝW.V.T ➡*[h, g] U.
#h #g #a #G #L #V #W #T #U #H
elim (cpxs_inv_appl1 … H) -H *
[ #V0 #T0 #_ #_ #H destruct /2 width=1 by tsts_pair, or_introl/
| #b #W0 #T0 #HT0 #HU
  elim (cpxs_inv_abst1 … HT0) -HT0 #W1 #T1 #HW1 #HT1 #H destruct
  lapply (lsubr_cpxs_trans … HT1 (L.ⓓⓝW.V) ?) -HT1
  /5 width=3 by cpxs_trans, cpxs_bind, cpxs_pair_sn, lsubr_beta, or_intror/
| #b #V1 #V2 #V0 #T1 #_ #_ #HT1 #_
  elim (cpxs_inv_abst1 … HT1) -HT1 #W2 #T2 #_ #_ #H destruct
]
qed-.

(* Note: probably this is an inversion lemma *)
lemma cpxs_fwd_delta: ∀h,g,I,G,L,K,V1,i. ⇩[i] L ≡ K.ⓑ{I}V1 →
                      ∀V2. ⇧[0, i + 1] V1 ≡ V2 →
                      ∀U. ⦃G, L⦄ ⊢ #i ➡*[h, g] U →
                      #i ≂ U ∨ ⦃G, L⦄ ⊢ V2 ➡*[h, g] U.
#h #g #I #G #L #K #V1 #i #HLK #V2 #HV12 #U #H
elim (cpxs_inv_lref1 … H) -H /2 width=1 by or_introl/
* #I0 #K0 #V0 #U0 #HLK0 #HVU0 #HU0
lapply (drop_mono … HLK0 … HLK) -HLK0 #H destruct
/4 width=10 by cpxs_lift, drop_fwd_drop2, or_intror/
qed-.

lemma cpxs_fwd_theta: ∀h,g,a,G,L,V1,V,T,U. ⦃G, L⦄ ⊢ ⓐV1.ⓓ{a}V.T ➡*[h, g] U →
                      ∀V2. ⇧[0, 1] V1 ≡ V2 → ⓐV1.ⓓ{a}V.T ≂ U ∨
                      ⦃G, L⦄ ⊢ ⓓ{a}V.ⓐV2.T ➡*[h, g] U.
#h #g #a #G #L #V1 #V #T #U #H #V2 #HV12
elim (cpxs_inv_appl1 … H) -H *
[ -HV12 #V0 #T0 #_ #_ #H destruct /2 width=1 by tsts_pair, or_introl/
| #b #W #T0 #HT0 #HU
  elim (cpxs_inv_abbr1 … HT0) -HT0 *
  [ #V3 #T3 #_ #_ #H destruct
  | #X #HT2 #H #H0 destruct
    elim (lift_inv_bind1 … H) -H #W2 #T2 #HW2 #HT02 #H destruct
    @or_intror @(cpxs_trans … HU) -U (**) (* explicit constructor *)
    @(cpxs_trans … (+ⓓV.ⓐV2.ⓛ{b}W2.T2)) [ /3 width=1 by cpxs_flat_dx, cpxs_bind_dx/ ] -T
    @(cpxs_strap2 … (ⓐV1.ⓛ{b}W.T0)) [2: /2 width=1 by cpxs_beta_dx/ ]
    /4 width=7 by cpx_zeta, lift_bind, lift_flat/
  ]
| #b #V3 #V4 #V0 #T0 #HV13 #HV34 #HT0 #HU
  @or_intror @(cpxs_trans … HU) -U (**) (* explicit constructor *)
  elim (cpxs_inv_abbr1 … HT0) -HT0 *
  [ #V5 #T5 #HV5 #HT5 #H destruct
    lapply (cpxs_lift … HV13 (L.ⓓV) … HV12 … HV34) -V1 -V3
    /3 width=2 by cpxs_flat, cpxs_bind, drop_drop/
  | #X #HT1 #H #H0 destruct
    elim (lift_inv_bind1 … H) -H #V5 #T5 #HV05 #HT05 #H destruct
    lapply (cpxs_lift … HV13 (L.ⓓV0) … HV12 … HV34) -V3 /2 width=2 by drop_drop/ #HV24
    @(cpxs_trans … (+ⓓV.ⓐV2.ⓓ{b}V5.T5)) [ /3 width=1 by cpxs_flat_dx, cpxs_bind_dx/ ] -T
    @(cpxs_strap2 … (ⓐV1.ⓓ{b}V0.T0)) [ /4 width=7 by cpx_zeta, lift_bind, lift_flat/ ] -V -V5 -T5
    @(cpxs_strap2 … (ⓓ{b}V0.ⓐV2.T0)) /3 width=3 by cpxs_pair_sn, cpxs_bind_dx, cpr_cpx, cpr_theta/
  ]
]
qed-.

lemma cpxs_fwd_cast: ∀h,g,G,L,W,T,U. ⦃G, L⦄ ⊢ ⓝW.T ➡*[h, g] U →
                     ∨∨ ⓝW. T ≂ U | ⦃G, L⦄ ⊢ T ➡*[h, g] U | ⦃G, L⦄ ⊢ W ➡*[h, g] U.
#h #g #G #L #W #T #U #H
elim (cpxs_inv_cast1 … H) -H /2 width=1 by or3_intro1, or3_intro2/ *
#W0 #T0 #_ #_ #H destruct /2 width=1 by tsts_pair, or3_intro0/
qed-.
