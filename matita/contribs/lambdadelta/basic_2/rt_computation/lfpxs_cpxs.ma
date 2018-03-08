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

include "basic_2/rt_computation/cpxs_lfpx.ma".
include "basic_2/rt_computation/lfpxs_fqup.ma".

(* UNCOUNTED PARALLEL RT-COMPUTATION FOR LOCAL ENV.S ON REFERRED ENTRIES ****)

(* Properties with uncounted context-sensitive rt-computation for terms *****)

(* Basic_2A1: uses: lpxs_pair lpxs_pair_refl *)
lemma lfpxs_pair_refl: ∀h,G,L,V1,V2. ⦃G, L⦄ ⊢ V1 ⬈*[h] V2 →
                       ∀I,T. ⦃G, L.ⓑ{I}V1⦄ ⊢ ⬈*[h, T] L.ⓑ{I}V2.
/2 width=1 by tc_lfxs_pair_refl/ qed.

lemma lfpxs_cpx_trans: ∀h,G. s_r_transitive … (cpx h G) (lfpxs h G).
#h #G @s_r_trans_LTC2 @lfpx_cpxs_trans (**) (* auto fails *)
qed-.

(* Note: lfpxs_cpx_conf does not hold, thus we cannot invoke s_r_trans_LTC1 *)
lemma lfpxs_cpxs_trans: ∀h,G. s_rs_transitive … (cpx h G) (lfpxs h G).
#h #G @s_r_to_s_rs_trans @s_r_trans_LTC2
@s_rs_trans_TC1 /2 width=3 by lfpx_cpxs_trans/ (**) (* full auto too slow *)
qed-.

(* Advanced properties on uncounted rt-computation for terms ****************)

lemma cpxs_bind2: ∀h,G,L,V1,V2. ⦃G, L⦄ ⊢ V1 ⬈*[h] V2 →
                  ∀I,T1,T2. ⦃G, L.ⓑ{I}V2⦄ ⊢ T1 ⬈*[h] T2 →
                  ∀p. ⦃G, L⦄ ⊢ ⓑ{p,I}V1.T1 ⬈*[h] ⓑ{p,I}V2.T2.
/4 width=3 by lfpxs_cpxs_trans, lfpxs_pair_refl, cpxs_bind/ qed.

(* Advanced inversion lemmas on uncounted rt-computation for terms **********)

lemma cpxs_inv_abst1: ∀h,p,G,L,V1,T1,U2. ⦃G, L⦄ ⊢ ⓛ{p}V1.T1 ⬈*[h] U2 →
                      ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ⬈*[h] V2 & ⦃G, L.ⓛV1⦄ ⊢ T1 ⬈*[h] T2 &
                               U2 = ⓛ{p}V2.T2.
#h #p #G #L #V1 #T1 #U2 #H @(cpxs_ind … H) -U2 /2 width=5 by ex3_2_intro/
#U0 #U2 #_ #HU02 * #V0 #T0 #HV10 #HT10 #H destruct
elim (cpx_inv_abst1 … HU02) -HU02 #V2 #T2 #HV02 #HT02 #H destruct
lapply (lfpxs_cpx_trans … HT02 (L.ⓛV1) ?)
/3 width=5 by lfpxs_pair_refl, cpxs_trans, cpxs_strap1, ex3_2_intro/
qed-.

lemma cpxs_inv_abbr1: ∀h,p,G,L,V1,T1,U2. ⦃G, L⦄ ⊢ ⓓ{p}V1.T1 ⬈*[h] U2 → (
                      ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ⬈*[h] V2 & ⦃G, L.ⓓV1⦄ ⊢ T1 ⬈*[h] T2 &
                               U2 = ⓓ{p}V2.T2
                      ) ∨
                      ∃∃T2. ⦃G, L.ⓓV1⦄ ⊢ T1 ⬈*[h] T2 & ⬆*[1] U2 ≡ T2 & p = true.
#h #p #G #L #V1 #T1 #U2 #H @(cpxs_ind … H) -U2 /3 width=5 by ex3_2_intro, or_introl/
#U0 #U2 #_ #HU02 * *
[ #V0 #T0 #HV10 #HT10 #H destruct
  elim (cpx_inv_abbr1 … HU02) -HU02 *
  [ #V2 #T2 #HV02 #HT02 #H destruct
    lapply (lfpxs_cpx_trans … HT02 (L.ⓓV1) ?)
    /4 width=5 by lfpxs_pair_refl, cpxs_trans, cpxs_strap1, ex3_2_intro, or_introl/
  | #T2 #HT02 #HUT2
    lapply (lfpxs_cpx_trans … HT02 (L.ⓓV1) ?) -HT02
    /4 width=3 by lfpxs_pair_refl, cpxs_trans, ex3_intro, or_intror/
  ]
| #U1 #HTU1 #HU01
  elim (cpx_lifts_sn … HU02 (Ⓣ) … (L.ⓓV1) … HU01)
  /4 width=3 by cpxs_strap1, drops_refl, drops_drop, ex3_intro, or_intror/
]
qed-.
