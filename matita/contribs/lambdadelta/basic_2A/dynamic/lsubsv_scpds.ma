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

include "basic_2A/static/lsubd_da.ma".
include "basic_2A/dynamic/lsubsv_lsubd.ma".
include "basic_2A/dynamic/lsubsv_lstas.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR STRATIFIED NATIVE VALIDITY **************)

(* Properties on decomposed extended parallel computation on terms **********)

lemma lsubsv_scpds_trans: ∀h,g,G,L2,T1,T2,d. ⦃G, L2⦄ ⊢ T1 •*➡*[h, g, d] T2 →
                          ∀L1. G ⊢ L1 ⫃¡[h, g] L2 →
                          ∃∃T. ⦃G, L1⦄ ⊢ T1 •*➡*[h, g, d] T & ⦃G, L1⦄ ⊢ T2 ➡* T.
#h #g #G #L2 #T1 #T2 #d2 * #T #d1 #Hd21 #Hd1 #HT1 #HT2 #L1 #HL12
lapply (lsubsv_cprs_trans … HL12 … HT2) -HT2 #HT2
elim (lsubsv_lstas_trans … HT1 … Hd1 … HL12) // #T0 #HT10 #HT0
lapply (cpcs_cprs_strap1 … HT0 … HT2) -T #HT02
elim (cpcs_inv_cprs … HT02) -HT02
/5 width=5 by lsubsv_fwd_lsubd, lsubd_da_trans, ex4_2_intro, ex2_intro/
qed-.
