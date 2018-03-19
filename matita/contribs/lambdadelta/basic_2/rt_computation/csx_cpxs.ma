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

include "basic_2/rt_computation/cpxs_tdeq.ma".
include "basic_2/rt_computation/cpxs_cpxs.ma".
include "basic_2/rt_computation/csx_csx.ma".

(* UNCOUNTED CONTEXT-SENSITIVE PARALLEL RT-COMPUTATION FOR TERMS ************)

(* Properties with uncounted context-sensitive rt-computation for terms *****)

(* Basic_1: was just: sn3_intro *)
lemma csx_intro_cpxs: ∀h,o,G,L,T1.
                      (∀T2. ⦃G, L⦄ ⊢ T1 ⬈*[h] T2 → (T1 ≛[h, o] T2 → ⊥) → ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃T2⦄) →
                      ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃T1⦄.
/4 width=1 by cpx_cpxs, csx_intro/ qed-.

(* Basic_1: was just: sn3_pr3_trans *)
lemma csx_cpxs_trans: ∀h,o,G,L,T1. ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃T1⦄ →
                      ∀T2. ⦃G, L⦄ ⊢ T1 ⬈*[h] T2 → ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃T2⦄.
#h #o #G #L #T1 #HT1 #T2 #H @(cpxs_ind … H) -T2
/2 width=3 by csx_cpx_trans/
qed-.

(* Eliminators with uncounted context-sensitive rt-computation for terms ****)

lemma csx_ind_cpxs_tdeq: ∀h,o,G,L. ∀R:predicate term.
                         (∀T1. ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃T1⦄ →
                               (∀T2. ⦃G, L⦄ ⊢ T1 ⬈*[h] T2 → (T1 ≛[h, o] T2 → ⊥) → R T2) → R T1
                         ) →
                         ∀T1. ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃T1⦄ →
                         ∀T0. ⦃G, L⦄ ⊢ T1 ⬈*[h] T0 → ∀T2. T0 ≛[h, o] T2 → R T2.
#h #o #G #L #R #IH #T1 #H @(csx_ind … H) -T1
#T1 #HT1 #IH1 #T0 #HT10 #T2 #HT02
@IH -IH /3 width=3 by csx_cpxs_trans, csx_tdeq_trans/ -HT1 #V2 #HTV2 #HnTV2
lapply (tdeq_tdneq_trans … HT02 … HnTV2) -HnTV2 #H
elim (tdeq_cpxs_trans … HT02 … HTV2) -T2 #V0 #HTV0 #HV02
lapply (tdneq_tdeq_canc_dx … H … HV02) -H #HnTV0
elim (tdeq_dec h o T1 T0) #H
[ lapply (tdeq_tdneq_trans … H … HnTV0) -H -HnTV0 #Hn10
  lapply (cpxs_trans … HT10 … HTV0) -T0 #H10
  elim (cpxs_tdneq_fwd_step_sn … H10 …  Hn10) -H10 -Hn10
  /3 width=8 by tdeq_trans/
| elim (cpxs_tdneq_fwd_step_sn … HT10 … H) -HT10 -H #T #V #HT1 #HnT1 #HTV #HVT0
  elim (tdeq_cpxs_trans … HVT0 … HTV0) -T0
  /3 width=8 by cpxs_trans, tdeq_trans/
]
qed-.

(* Basic_2A1: was: csx_ind_alt *)
lemma csx_ind_cpxs: ∀h,o,G,L. ∀R:predicate term.
                    (∀T1. ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃T1⦄ →
                          (∀T2. ⦃G, L⦄ ⊢ T1 ⬈*[h] T2 → (T1 ≛[h, o] T2 → ⊥) → R T2) → R T1
                    ) →
                    ∀T. ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃T⦄ → R T.
#h #o #G #L #R #IH #T #HT
@(csx_ind_cpxs_tdeq … IH … HT) -IH -HT // (**) (* full auto fails *)
qed-.
