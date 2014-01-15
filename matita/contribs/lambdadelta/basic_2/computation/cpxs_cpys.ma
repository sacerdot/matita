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

include "basic_2/substitution/cpys_cpys.ma".
include "basic_2/computation/cpxs_cpxs.ma".

(* SN EXTENDED PARALLEL REDUCTION FOR LOCAL ENVIRONMENTS ********************)

(* Main properties **********************************************************)

lemma cpx_fwd_cpys_tpxs: ∀h,g,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡[h, g] T2 →
                         ∃∃T. ⦃G, L⦄ ⊢ T1 ▶*×[0, ∞] T & ⦃G, ⋆⦄ ⊢ T ➡*[h, g] T2.
#h #g #G #L #T1 #T2 #H elim H -G -L -T1 -T2
[ /2 width=3 by ex2_intro/
| /4 width=3 by cpx_cpxs, cpx_sort, ex2_intro/
| #I #G #L #K #V1 #V2 #W2 #i #HLK #_ #HVW2 * #V #HV1 #HV2
  elim (lift_total V 0 (i+1)) #W #HVW
  @(ex2_intro … W) /2 width=7 by cpys_subst_Y2/
| #a #I #G #L #V1 #V2 #T1 #T2 #_ #_ * #V #HV1 #HV2 * #T #HT1 #HT2
  elim (cpys_split_up … HT1 1) -HT1 // #T0 #HT10 #HT0
  @(ex2_intro … (ⓑ{a,I}V.T0))
  [ @(cpys_bind … HV1) -HV1
  | @(cpxs_bind … HV2) -HV2
  ]  
