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

include "basic_2/static/ssta_ltpss_dx.ma".
include "basic_2/unwind/sstas.ma".

(* ITERATED STRATIFIED STATIC TYPE ASSIGNMENT FOR TERMS *********************)

(* Properties about dx parallel unfold **************************************)

lemma sstas_ltpss_dx_tpss_conf: ∀h,g,L1,T1,U1. ⦃h, L1⦄ ⊢ T1 •*[g] U1 →
                                ∀L2,d,e. L1 ▶* [d, e] L2 →
                                ∀T2. L2 ⊢ T1 ▶* [d, e] T2 →
                                ∃∃U2. ⦃h, L2⦄ ⊢ T2 •*[g] U2 &
                                      L2 ⊢ U1 ▶* [d, e] U2.
#h #g #L1 #T1 #U1 #H @(sstas_ind_dx … H) -T1 /2 width=3/
#T0 #U0 #l0 #HTU0 #_ #IHU01 #L2 #d #e #HL12 #T #HT0
elim (ssta_ltpss_dx_tpss_conf … HTU0 … HL12 … HT0) -HTU0 -HT0 #U #HTU #HU0
elim (IHU01 … HL12 … HU0) -IHU01 -HL12 -U0 /3 width=4/
qed.

lemma sstas_ltpss_dx_tps_conf: ∀h,g,L1,T1,U1. ⦃h, L1⦄ ⊢ T1 •*[g] U1 →
                               ∀L2,d,e. L1 ▶* [d, e] L2 →
                               ∀T2. L2 ⊢ T1 ▶ [d, e] T2 →
                               ∃∃U2. ⦃h, L2⦄ ⊢ T2 •*[g] U2 & L2 ⊢ U1 ▶* [d, e] U2.
/3 width=7 by step, sstas_ltpss_dx_tpss_conf/ qed. (**) (* auto fails without trace *)

lemma sstas_ltpss_dx_conf: ∀h,g,L1,T,U1. ⦃h, L1⦄ ⊢ T •*[g] U1 →
                           ∀L2,d,e. L1 ▶* [d, e] L2 →
                           ∃∃U2. ⦃h, L2⦄ ⊢ T •*[g] U2 & L2 ⊢ U1 ▶* [d, e] U2.
/2 width=5/ qed.

lemma sstas_tpss_conf: ∀h,g,L,T1,U1. ⦃h, L⦄ ⊢ T1 •*[g] U1 →
                       ∀T2,d,e. L ⊢ T1 ▶* [d, e] T2 →
                       ∃∃U2. ⦃h, L⦄ ⊢ T2 •*[g] U2 & L ⊢ U1 ▶* [d, e] U2.
/2 width=5/ qed.

lemma sstas_tps_conf: ∀h,g,L,T1,U1. ⦃h, L⦄ ⊢ T1 •*[g] U1 →
                      ∀T2,d,e. L ⊢ T1 ▶ [d, e] T2 →
                      ∃∃U2. ⦃h, L⦄ ⊢ T2 •*[g] U2 & L ⊢ U1 ▶* [d, e] U2.
/2 width=5/ qed.
