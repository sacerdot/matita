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

include "basic_2/rt_computation/cpme_aaa.ma".
include "basic_2/rt_computation/cpre_cpre.ma".
include "basic_2/rt_equivalence/cpes.ma".
include "basic_2/dynamic/cnv_cpme.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

(* Properties with t-bound rt-equivalence for terms *************************)

lemma cnv_cpes_dec (a) (h) (n1) (n2) (G) (L):
      ∀T1. ⦃G,L⦄ ⊢ T1 ![a,h] → ∀T2. ⦃G,L⦄ ⊢ T2 ![a,h] →
      Decidable … (⦃G,L⦄ ⊢ T1 ⬌*[h,n1,n2] T2).
#a #h #n1 #n2 #G #L #T1 #HT1 #T2 #HT2
elim (cnv_fwd_aaa … HT1) #A1 #HA1
elim (cnv_fwd_aaa … HT2) #A2 #HA2
elim (cpme_total_aaa h n1 … HA1) -HA1 #U1 #HTU1
elim (cpme_total_aaa h n2 … HA2) -HA2 #U2 #HTU2
elim (eq_term_dec U1 U2) [ #H destruct | #HnU12 ]
[ cases HTU1 -HTU1 #HTU1 #_
  cases HTU2 -HTU2 #HTU2 #_
  /3 width=3 by cpms_div, or_introl/
| @or_intror * #T0 #HT10 #HT20
  lapply (cnv_cpme_cpms_conf … HT1 … HT10 … HTU1) -T1 #H1
  lapply (cnv_cpme_cpms_conf … HT2 … HT20 … HTU2) -T2 #H2
  /3 width=6 by cpre_mono/
]
qed-.
