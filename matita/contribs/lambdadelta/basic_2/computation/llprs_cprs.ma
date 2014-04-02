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

include "basic_2/relocation/llpx_sn_tc.ma".
include "basic_2/computation/cprs_cprs.ma".
include "basic_2/computation/llprs.ma".

(* LAZY SN PARALLEL COMPUTATION ON LOCAL ENVIRONMENTS ***********************)

(* Advanced properties ******************************************************)

lemma llprs_pair_dx: ∀G,L,V1,V2. ⦃G, L⦄ ⊢ V1 ➡* V2 →
                     ∀I,T. ⦃G, L.ⓑ{I}V1⦄ ⊢ ➡*[T, 0] L.ⓑ{I}V2.
/2 width=1 by llpx_sn_TC_pair_dx/ qed.

(* Properties on context-sensitive parallel computation for terms ***********)

lemma llprs_cpr_trans: ∀G. s_r_transitive … (cpr G) (llprs G 0).
/3 width=5 by cprs_llpr_trans, s_r_trans_LTC2/ qed-.

(* Basic_1: was just: pr3_pr3_pr3_t *)
lemma llprs_cprs_trans: ∀G. s_rs_transitive … (cpr G) (llprs G 0).
#G @s_r_to_s_rs_trans @s_r_trans_LTC2
/3 width=5 by cprs_llpr_trans, s_rs_trans_TC1/ (**) (* full auto too slow *)
qed-.

lemma cprs_bind2: ∀G,L,V1,V2. ⦃G, L⦄ ⊢ V1 ➡* V2 →
                  ∀I,T1,T2. ⦃G, L.ⓑ{I}V2⦄ ⊢ T1 ➡* T2 →
                  ∀a. ⦃G, L⦄ ⊢ ⓑ{a,I}V1.T1 ➡* ⓑ{a,I}V2.T2.
/4 width=3 by llprs_cprs_trans, llprs_pair_dx, cprs_bind/ qed.

(* Inversion lemmas on context-sensitive parallel computation for terms *****)

(* Basic_1: was: pr3_gen_abst *)
lemma cprs_inv_abst1: ∀a,G,L,W1,T1,U2. ⦃G, L⦄ ⊢ ⓛ{a}W1.T1 ➡* U2 →
                      ∃∃W2,T2. ⦃G, L⦄ ⊢ W1 ➡* W2 & ⦃G, L.ⓛW1⦄ ⊢ T1 ➡* T2 &
                               U2 = ⓛ{a}W2.T2.
#a #G #L #V1 #T1 #U2 #H @(cprs_ind … H) -U2 /2 width=5 by ex3_2_intro/
#U0 #U2 #_ #HU02 * #V0 #T0 #HV10 #HT10 #H destruct
elim (cpr_inv_abst1 … HU02) -HU02 #V2 #T2 #HV02 #HT02 #H destruct
lapply (llprs_cpr_trans … HT02 (L.ⓛV1) ?)
/3 width=5 by llprs_pair_dx, cprs_trans, cprs_strap1, ex3_2_intro/
qed-.

lemma cprs_inv_abst: ∀a,G,L,W1,W2,T1,T2. ⦃G, L⦄ ⊢ ⓛ{a}W1.T1 ➡* ⓛ{a}W2.T2 →
                     ⦃G, L⦄ ⊢ W1 ➡* W2 ∧ ⦃G, L.ⓛW1⦄ ⊢ T1 ➡* T2.
#a #G #L #W1 #W2 #T1 #T2 #H
elim (cprs_inv_abst1 … H) -H #W #T #HW1 #HT1 #H destruct /2 width=1 by conj/
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
    lapply (llprs_cpr_trans … HT02 (L.ⓓV1) ?)
    /4 width=5 by llprs_pair_dx, cprs_trans, cprs_strap1, ex3_2_intro, or_introl/
  | #T2 #HT02 #HUT2
    lapply (llprs_cpr_trans … HT02 (L.ⓓV1) ?) -HT02
    /4 width=3 by llprs_pair_dx, cprs_trans, ex3_intro, or_intror/
  ]
| #U1 #HTU1 #HU01
  elim (lift_total U2 0 1) #U #HU2
  lapply (cpr_lift … HU02 (L.ⓓV1) … HU01 … HU2) -U0
  /4 width=3 by cprs_strap1, ldrop_drop, ex3_intro, or_intror/
]
qed-.
