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

(* CONTEXT_SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

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
