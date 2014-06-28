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

include "basic_2/computation/cprs_cprs.ma".
include "basic_2/computation/lprs.ma".

(* SN PARALLEL COMPUTATION ON LOCAL ENVIRONMENTS ****************************)

(* Advanced properties ******************************************************)

lemma lprs_pair: ∀I,G,L1,L2. ⦃G, L1⦄ ⊢ ➡* L2 →
                 ∀V1,V2. ⦃G, L1⦄ ⊢ V1 ➡* V2 → ⦃G, L1.ⓑ{I}V1⦄ ⊢ ➡* L2.ⓑ{I}V2.
/2 width=1 by TC_lpx_sn_pair/ qed.

(* Advanced inversion lemmas ************************************************)

lemma lprs_inv_pair1: ∀I,G,K1,L2,V1. ⦃G, K1.ⓑ{I}V1⦄ ⊢ ➡* L2 →
                      ∃∃K2,V2. ⦃G, K1⦄ ⊢ ➡* K2 & ⦃G, K1⦄ ⊢ V1 ➡* V2 &
                               L2 = K2.ⓑ{I}V2.
/3 width=3 by TC_lpx_sn_inv_pair1, lpr_cprs_trans/ qed-.

lemma lprs_inv_pair2: ∀I,G,L1,K2,V2. ⦃G, L1⦄ ⊢ ➡* K2.ⓑ{I}V2 →
                      ∃∃K1,V1. ⦃G, K1⦄ ⊢ ➡* K2 & ⦃G, K1⦄ ⊢ V1 ➡* V2 &
                               L1 = K1.ⓑ{I}V1.
/3 width=3 by TC_lpx_sn_inv_pair2, lpr_cprs_trans/ qed-.

(* Advanced eliminators *****************************************************)

lemma lprs_ind_alt: ∀G. ∀R:relation lenv.
                    R (⋆) (⋆) → (
                       ∀I,K1,K2,V1,V2.
                       ⦃G, K1⦄ ⊢ ➡* K2 → ⦃G, K1⦄ ⊢ V1 ➡* V2 →
                       R K1 K2 → R (K1.ⓑ{I}V1) (K2.ⓑ{I}V2)
                    ) →
                    ∀L1,L2. ⦃G, L1⦄ ⊢ ➡* L2 → R L1 L2.
/3 width=4 by TC_lpx_sn_ind, lpr_cprs_trans/ qed-.

(* Properties on context-sensitive parallel computation for terms ***********)

lemma lprs_cpr_trans: ∀G. s_r_transitive … (cpr G) (λ_. lprs G).
/3 width=5 by s_r_trans_LTC2, lpr_cprs_trans/ qed-.

(* Basic_1: was just: pr3_pr3_pr3_t *)
(* Note: alternative proof /3 width=5 by s_r_trans_LTC1, lprs_cpr_trans/ *)
lemma lprs_cprs_trans: ∀G. s_rs_transitive … (cpr G) (λ_. lprs G).
#G @s_r_to_s_rs_trans @s_r_trans_LTC2
@s_rs_trans_TC1 /2 width=3 by lpr_cprs_trans/ (**) (* full auto too slow *)
qed-.

lemma lprs_cprs_conf_dx: ∀G,L0,T0,T1. ⦃G, L0⦄ ⊢ T0 ➡* T1 →
                         ∀L1. ⦃G, L0⦄ ⊢ ➡* L1 →
                         ∃∃T. ⦃G, L1⦄ ⊢ T1 ➡* T & ⦃G, L1⦄ ⊢ T0 ➡* T.
#G #L0 #T0 #T1 #HT01 #L1 #H @(lprs_ind … H) -L1 /2 width=3 by ex2_intro/
#L #L1 #_ #HL1 * #T #HT1 #HT0 -L0
elim (cprs_lpr_conf_dx … HT1 … HL1) -HT1 #T2 #HT2
elim (cprs_lpr_conf_dx … HT0 … HL1) -L #T3 #HT3
elim (cprs_conf … HT2 … HT3) -T
/3 width=5 by cprs_trans, ex2_intro/
qed-.

lemma lprs_cpr_conf_dx: ∀G,L0,T0,T1. ⦃G, L0⦄ ⊢ T0 ➡ T1 →
                        ∀L1. ⦃G, L0⦄ ⊢ ➡* L1 →
                        ∃∃T. ⦃G, L1⦄ ⊢ T1 ➡* T & ⦃G, L1⦄ ⊢ T0 ➡* T.
/3 width=3 by lprs_cprs_conf_dx, cpr_cprs/ qed-.

(* Note: this can be proved on its own using lprs_ind_dx *)
lemma lprs_cprs_conf_sn: ∀G,L0,T0,T1. ⦃G, L0⦄ ⊢ T0 ➡* T1 →
                         ∀L1. ⦃G, L0⦄ ⊢ ➡* L1 →
                         ∃∃T. ⦃G, L0⦄ ⊢ T1 ➡* T & ⦃G, L1⦄ ⊢ T0 ➡* T.
#G #L0 #T0 #T1 #HT01 #L1 #HL01
elim (lprs_cprs_conf_dx … HT01 … HL01) -HT01
/3 width=3 by lprs_cprs_trans, ex2_intro/
qed-.

lemma lprs_cpr_conf_sn: ∀G,L0,T0,T1. ⦃G, L0⦄ ⊢ T0 ➡ T1 →
                        ∀L1. ⦃G, L0⦄ ⊢ ➡* L1 →
                        ∃∃T. ⦃G, L0⦄ ⊢ T1 ➡* T & ⦃G, L1⦄ ⊢ T0 ➡* T.
/3 width=3 by lprs_cprs_conf_sn, cpr_cprs/ qed-.

lemma cprs_bind2: ∀G,L,V1,V2. ⦃G, L⦄ ⊢ V1 ➡* V2 →
                  ∀I,T1,T2. ⦃G, L.ⓑ{I}V2⦄ ⊢ T1 ➡* T2 →
                  ∀a. ⦃G, L⦄ ⊢ ⓑ{a,I}V1.T1 ➡* ⓑ{a,I}V2.T2.
/4 width=5 by lprs_cprs_trans, lprs_pair, cprs_bind/ qed.

(* Inversion lemmas on context-sensitive parallel computation for terms *****)

(* Basic_1: was: pr3_gen_abst *)
lemma cprs_inv_abst1: ∀a,G,L,W1,T1,U2. ⦃G, L⦄ ⊢ ⓛ{a}W1.T1 ➡* U2 →
                      ∃∃W2,T2. ⦃G, L⦄ ⊢ W1 ➡* W2 & ⦃G, L.ⓛW1⦄ ⊢ T1 ➡* T2 &
                               U2 = ⓛ{a}W2.T2.
#a #G #L #V1 #T1 #U2 #H @(cprs_ind … H) -U2 /2 width=5 by ex3_2_intro/
#U0 #U2 #_ #HU02 * #V0 #T0 #HV10 #HT10 #H destruct
elim (cpr_inv_abst1 … HU02) -HU02 #V2 #T2 #HV02 #HT02 #H destruct
lapply (lprs_cpr_trans … HT02 (L.ⓛV1) ?)
/3 width=5 by lprs_pair, cprs_trans, cprs_strap1, ex3_2_intro/
qed-.

lemma cprs_inv_abst: ∀a,G,L,W1,W2,T1,T2. ⦃G, L⦄ ⊢ ⓛ{a}W1.T1 ➡* ⓛ{a}W2.T2 →
                     ⦃G, L⦄ ⊢ W1 ➡* W2 ∧ ⦃G, L.ⓛW1⦄ ⊢ T1 ➡* T2.
#a #G #L #W1 #W2 #T1 #T2 #H elim (cprs_inv_abst1 … H) -H
#W #T #HW1 #HT1 #H destruct /2 width=1 by conj/
qed-.

(* Basic_1: was pr3_gen_abbr *)
lemma cprs_inv_abbr1: ∀a,G,L,V1,T1,U2. ⦃G, L⦄ ⊢ ⓓ{a}V1.T1 ➡* U2 → (
                      ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ➡* V2 & ⦃G, L.ⓓV1⦄ ⊢ T1 ➡* T2 &
                               U2 = ⓓ{a}V2.T2
                      ) ∨
                      ∃∃T2. ⦃G, L.ⓓV1⦄ ⊢ T1 ➡* T2 & ⇧[0, 1] U2 ≡ T2 & a = true.
#a #G #L #V1 #T1 #U2 #H @(cprs_ind … H) -U2 /3 width=5 by ex3_2_intro, or_introl/
#U0 #U2 #_ #HU02 * *
[ #V0 #T0 #HV10 #HT10 #H destruct
  elim (cpr_inv_abbr1 … HU02) -HU02 *
  [ #V2 #T2 #HV02 #HT02 #H destruct
    lapply (lprs_cpr_trans … HT02 (L.ⓓV1) ?)
    /4 width=5 by lprs_pair, cprs_trans, cprs_strap1, ex3_2_intro, or_introl/
  | #T2 #HT02 #HUT2
    lapply (lprs_cpr_trans … HT02 (L.ⓓV1) ?) -HT02
    /4 width=3 by lprs_pair, cprs_trans, ex3_intro, or_intror/
  ]
| #U1 #HTU1 #HU01 elim (lift_total U2 0 1)
  #U #HU2 lapply (cpr_lift … HU02 (L.ⓓV1) … HU01 … HU2) -U0
  /4 width=3 by cprs_strap1, drop_drop, ex3_intro, or_intror/
]
qed-.

(* More advanced properties *************************************************)

lemma lprs_pair2: ∀I,G,L1,L2. ⦃G, L1⦄ ⊢ ➡* L2 →
                  ∀V1,V2. ⦃G, L2⦄ ⊢ V1 ➡* V2 → ⦃G, L1.ⓑ{I}V1⦄ ⊢ ➡* L2.ⓑ{I}V2.
/3 width=3 by lprs_pair, lprs_cprs_trans/ qed.
