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
include "basic_2/rt_computation/cnuw_cnuw.ma".
include "basic_2/rt_computation/cpmuwe.ma".
include "basic_2/dynamic/cnv_cpme.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

(* Advanced Properties with t-unbound whd evaluation on terms ***************)

lemma cnv_R_cpmuwe_dec (a) (h) (G) (L):
      ∀T. ⦃G,L⦄ ⊢ T ![a,h] → ∀n. Decidable (R_cpmuwe h G L T n).
#a #h #G #L #T1 #HT1 #n
elim (cnv_fwd_aaa … HT1) #A #HA
elim (cpme_total_aaa h n … HA) -HA #T2 #HT12
elim (cnuw_dec h G L T2) #HnT1
[ /5 width=3 by cpme_fwd_cpms, cpmuwe_intro, ex_intro, or_introl/
| @or_intror * #T3 * #HT13 #HT3
  lapply (cnv_cpme_cpms_conf … HT1 … HT13 … HT12) -a -T1 #HT32
  /4 width=9 by cpme_fwd_cpms, cnuw_cpms_trans/
]
qed-.
