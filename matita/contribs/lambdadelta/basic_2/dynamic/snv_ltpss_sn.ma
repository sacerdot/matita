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

include "basic_2/dynamic/snv_ltpss_dx.ma".

(* STRATIFIED NATIVE VALIDITY FOR TERMS *************************************)

(* Properties about sn parallel unfold **************************************)

lemma snv_ltpss_sn_conf: ∀h,g,L1,L2,d,e. L1 ⊢ ▶* [d, e] L2 →
                         ∀T. ⦃h, L1⦄ ⊢ T ¡[g] → ⦃h, L2⦄ ⊢ T ¡[g].
#h #g #L1 #L2 #d #e #H
lapply (ltpss_sn_ltpssa … H) -H #H @(ltpssa_ind … H) -L2 //
#L #L2 #_ #HL2 #IHL1 #T1 #HT1
lapply (IHL1 … HT1) -IHL1 -HT1 #HT1
lapply (snv_ltpss_dx_conf … HT1 … HL2) -HT1 -HL2 //
qed-.
