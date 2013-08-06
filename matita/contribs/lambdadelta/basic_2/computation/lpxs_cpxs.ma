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

include "basic_2/computation/cpxs_cpxs.ma".
include "basic_2/computation/lpxs.ma".

(* SN EXTENDED PARALLEL COMPUTATION ON LOCAL ENVIRONMENTS *******************)

(* Advanced properties ******************************************************)

lemma lpxs_pair: ∀h,g,I,G,L1,L2. ⦃G, L1⦄ ⊢ ➡*[h, g] L2 →
                 ∀V1,V2. ⦃G, L1⦄ ⊢ V1 ➡*[h, g] V2 →
                 ⦃G, L1.ⓑ{I}V1⦄ ⊢ ➡*[h, g] L2.ⓑ{I}V2.
/2 width=1 by TC_lpx_sn_pair/ qed.

(* Advanced inversion lemmas ************************************************)

lemma lpxs_inv_pair1: ∀h,g,I,G,K1,L2,V1. ⦃G, K1.ⓑ{I}V1⦄ ⊢ ➡*[h, g] L2 →
                      ∃∃K2,V2. ⦃G, K1⦄ ⊢ ➡*[h, g] K2 & ⦃G, K1⦄ ⊢ V1 ➡*[h, g] V2 & L2 = K2.ⓑ{I}V2.
/3 width=3 by TC_lpx_sn_inv_pair1, lpx_cpxs_trans/ qed-.

lemma lpxs_inv_pair2: ∀h,g,I,G,L1,K2,V2. ⦃G, L1⦄ ⊢ ➡*[h, g] K2.ⓑ{I}V2 →
                      ∃∃K1,V1. ⦃G, K1⦄ ⊢ ➡*[h, g] K2 & ⦃G, K1⦄ ⊢ V1 ➡*[h, g] V2 & L1 = K1.ⓑ{I}V1.
/3 width=3 by TC_lpx_sn_inv_pair2, lpx_cpxs_trans/ qed-.

(* Properties on context-sensitive extended parallel computation for terms **)

lemma lpxs_cpx_trans: ∀h,g,G. s_r_trans … (cpx h g G) (lpxs h g G).
/3 width=5 by s_r_trans_TC2, lpx_cpxs_trans/ qed-.

lemma lpxs_cpxs_trans: ∀h,g,G. s_rs_trans … (cpx h g G) (lpxs h g G).
/3 width=5 by s_r_trans_TC1, lpxs_cpx_trans/ qed-.

lemma cpxs_bind2: ∀h,g,G,L,V1,V2. ⦃G, L⦄ ⊢ V1 ➡*[h, g] V2 →
                  ∀I,T1,T2. ⦃G, L.ⓑ{I}V2⦄ ⊢ T1 ➡*[h, g] T2 →
                  ∀a. ⦃G, L⦄ ⊢ ⓑ{a,I}V1.T1 ➡*[h, g] ⓑ{a,I}V2.T2.
#h #g #G #L #V1 #V2 #HV12 #I #T1 #T2 #HT12
lapply (lpxs_cpxs_trans … HT12 (L.ⓑ{I}V1) ?) /2 width=1/
qed.

(* Inversion lemmas on context-sensitive ext parallel computation for terms *)

lemma cpxs_inv_abst1: ∀h,g,a,G,L,V1,T1,U2. ⦃G, L⦄ ⊢ ⓛ{a}V1.T1 ➡*[h, g] U2 →
                      ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ➡*[h, g] V2 & ⦃G, L.ⓛV1⦄ ⊢ T1 ➡*[h, g] T2 &
                               U2 = ⓛ{a}V2.T2.
#h #g #a #G #L #V1 #T1 #U2 #H @(cpxs_ind … H) -U2 /2 width=5/
#U0 #U2 #_ #HU02 * #V0 #T0 #HV10 #HT10 #H destruct
elim (cpx_inv_abst1 … HU02) -HU02 #V2 #T2 #HV02 #HT02 #H destruct
lapply (lpxs_cpx_trans … HT02 (L.ⓛV1) ?) /2 width=1/ -HT02 #HT02
lapply (cpxs_strap1 … HV10 … HV02) -V0
lapply (cpxs_trans … HT10 … HT02) -T0 /2 width=5/
qed-.

lemma cpxs_inv_abbr1: ∀h,g,a,G,L,V1,T1,U2. ⦃G, L⦄ ⊢ ⓓ{a}V1.T1 ➡*[h, g] U2 → (
                      ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ➡*[h, g] V2 & ⦃G, L.ⓓV1⦄ ⊢ T1 ➡*[h, g] T2 &
                               U2 = ⓓ{a}V2.T2
                      ) ∨
                      ∃∃T2. ⦃G, L.ⓓV1⦄ ⊢ T1 ➡*[h, g] T2 & ⇧[0, 1] U2 ≡ T2 & a = true.
#h #g #a #G #L #V1 #T1 #U2 #H @(cpxs_ind … H) -U2 /3 width=5/
#U0 #U2 #_ #HU02 * *
[ #V0 #T0 #HV10 #HT10 #H destruct
  elim (cpx_inv_abbr1 … HU02) -HU02 *
  [ #V2 #T2 #HV02 #HT02 #H destruct
    lapply (lpxs_cpx_trans … HT02 (L.ⓓV1) ?) /2 width=1/ -HT02 #HT02
    lapply (cpxs_strap1 … HV10 … HV02) -V0
    lapply (cpxs_trans … HT10 … HT02) -T0 /3 width=5/
  | #T2 #HT02 #HUT2
    lapply (lpxs_cpx_trans … HT02 (L.ⓓV1) ?) -HT02 /2 width=1/ -V0 #HT02
    lapply (cpxs_trans … HT10 … HT02) -T0 /3 width=3/
  ]
| #U1 #HTU1 #HU01
  elim (lift_total U2 0 1) #U #HU2
  lapply (cpx_lift … HU02 (L.ⓓV1) … HU01 … HU2) -U0 /2 width=1/ /4 width=3/
]
qed-.

(* More advanced properties *************************************************)

lemma lpxs_pair2: ∀h,g,I,G,L1,L2. ⦃G, L1⦄ ⊢ ➡*[h, g] L2 →
                  ∀V1,V2. ⦃G, L2⦄ ⊢ V1 ➡*[h, g] V2 → ⦃G, L1.ⓑ{I}V1⦄ ⊢ ➡*[h, g] L2.ⓑ{I}V2.
/3 width=3 by lpxs_pair, lpxs_cpxs_trans/ qed.
