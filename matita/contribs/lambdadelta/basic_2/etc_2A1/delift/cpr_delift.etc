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

include "basic_2/unfold/thin_delift.ma".
include "basic_2/reducibility/tpr_delift.ma".
include "basic_2/reducibility/cpr.ma".

(* CONTEXT-SENSITIVE PARALLEL REDUCTION ON TERMS ****************************)

(* Properties on inverse basic term relocation ******************************)

(* Basic_1: was only: pr2_gen_cabbr *)
lemma thin_cpr_delift_conf: ∀L,U1,U2. L ⊢ U1 ➡ U2 →
                            ∀K,d,e. ▼*[d, e] L ≡ K → ∀T1. L ⊢ ▼*[d, e] U1 ≡ T1 →
                            ∃∃T2. K ⊢ T1 ➡ T2 & L ⊢ ▼*[d, e] U2 ≡ T2.
#L #U1 #U2 * #U #HU1 #HU2 #K #d #e #HLK #T1 #HTU1
elim (tpr_delift_conf … HU1 … HTU1) -U1 #T #HT1 #HUT
elim (le_or_ge (|L|) d) #Hd
[ elim (thin_delift_tpss_conf_le … HU2 … HUT … HLK ?)
| elim (le_or_ge (|L|) (d+e)) #Hde
  [ elim (thin_delift_tpss_conf_le_up … HU2 … HUT … HLK ? ? ?)
  | elim (thin_delift_tpss_conf_be … HU2 … HUT … HLK ? ?)
  ]
] -U -HLK // -Hd [2,3: -Hde] #T2 #HT2
lapply (cpr_intro … HT1 HT2) -T /2 width=3/
qed.
