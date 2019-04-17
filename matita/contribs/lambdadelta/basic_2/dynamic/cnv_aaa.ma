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

include "basic_2/rt_computation/cpms_aaa.ma".
include "basic_2/dynamic/cnv.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

(* Forward lemmas on atomic arity assignment for terms **********************)

(* Basic_2A1: uses: snv_fwd_aaa *)
lemma cnv_fwd_aaa (a) (h): ∀G,L,T. ⦃G, L⦄ ⊢ T ![a, h] → ∃A. ⦃G, L⦄ ⊢ T ⁝ A.
#a #h #G #L #T #H elim H -G -L -T
[ /2 width=2 by aaa_sort, ex_intro/
| #I #G #L #V #_ * /3 width=2 by aaa_zero, ex_intro/
| #I #G #L #K #_ * /3 width=2 by aaa_lref, ex_intro/
| #p * #G #L #V #T #_ #_ * #B #HV * #A #HA
  /3 width=2 by aaa_abbr, aaa_abst, ex_intro/
| #n #p #G #L #V #W #T0 #U0 #_ #_ #_ #HVW #HTU0 * #B #HV * #X #HT
  lapply (cpms_aaa_conf … HV … HVW) -HVW #H1W
  lapply (cpms_aaa_conf … HT … HTU0) -HTU0 #H
  elim (aaa_inv_abst … H) -H #B0 #A #H2W #HU #H destruct
  lapply (aaa_mono … H2W … H1W) -W #H destruct
  /3 width=4 by aaa_appl, ex_intro/
| #G #L #U #T #U0 #_ #_ #HU0 #HTU0 * #B #HU * #A #HT
  lapply (cpms_aaa_conf … HU … HU0) -HU0 #HU0
  lapply (cpms_aaa_conf … HT … HTU0) -HTU0 #H
  lapply (aaa_mono … H … HU0) -U0 #H destruct
  /3 width=3 by aaa_cast, ex_intro/
]
qed-.

(* Forward lemmas with t_bound rt_transition for terms **********************)

lemma cnv_fwd_cpm_SO (a) (h) (G) (L):
      ∀T. ⦃G, L⦄ ⊢ T ![a, h] → ∃U. ⦃G,L⦄ ⊢ T ➡[1,h] U.
#a #h #G #L #T #H
elim (cnv_fwd_aaa … H) -H #A #HA
/2 width=2 by aaa_cpm_SO/
qed-.

(* Forward lemmas with t_bound rt_computation for terms *********************)

lemma cnv_fwd_cpms_total (a) (h) (n) (G) (L):
      ∀T. ⦃G, L⦄ ⊢ T ![a, h] → ∃U. ⦃G,L⦄ ⊢ T ➡*[n,h] U.
#a #h #n #G #L #T #H
elim (cnv_fwd_aaa … H) -H #A #HA
/2 width=2 by cpms_total_aaa/
qed-.

(* Advanced inversion lemmas ************************************************)

lemma cnv_inv_appl_SO (a) (h) (G) (L):
      ∀V,T. ⦃G, L⦄ ⊢ ⓐV.T ![a, h] →
      ∃∃n,p,W0,U0. a = Ⓣ → n = 1 & ⦃G, L⦄ ⊢ V ![a, h] & ⦃G, L⦄ ⊢ T ![a, h] &
                   ⦃G, L⦄ ⊢ V ➡*[1, h] W0 & ⦃G, L⦄ ⊢ T ➡*[n, h] ⓛ{p}W0.U0.
* #h #G #L #V #T #H
elim (cnv_inv_appl … H) -H [ * [| #n ] | #n ] #p #W #U #Ha #HV #HT #HVW #HTU
[ elim (cnv_fwd_aaa … HT) #A #HA
  elim (aaa_cpm_SO h … (ⓛ{p}W.U))
  [|*: /2 width=8 by cpms_aaa_conf/ ] #X #HU0
  elim (cpm_inv_abst1 … HU0) #W0 #U0 #HW0 #_ #H0 destruct
  lapply (cpms_step_dx … HVW … HW0) -HVW -HW0 #HVW0
  lapply (cpms_step_dx … HTU … HU0) -HTU -HU0 #HTU0
  /2 width=7 by ex5_4_intro/
| lapply (Ha ?) -Ha [ // ] #Ha
  lapply (le_n_O_to_eq n ?) [ /3 width=1 by le_S_S_to_le/ ] -Ha #H destruct
  /2 width=7 by ex5_4_intro/
| @(ex5_4_intro … HV HT HVW HTU) #H destruct
]
qed-.

lemma cnv_inv_appl_true (h) (G) (L):
      ∀V,T. ⦃G,L⦄ ⊢ ⓐV.T ![h] →
      ∃∃p,W0,U0. ⦃G,L⦄ ⊢ V ![h] & ⦃G,L⦄ ⊢ T ![h] &
                   ⦃G,L⦄ ⊢ V ➡*[1,h] W0 & ⦃G,L⦄ ⊢ T ➡*[1,h] ⓛ{p}W0.U0.
#h #G #L #V #T #H
elim (cnv_inv_appl_SO … H) -H #n #p #W #U #Hn
>Hn -n [| // ] #HV #HT #HVW #HTU
/2 width=5 by ex4_3_intro/
qed-.
