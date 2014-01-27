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
include "basic_2/reduction/cpx_cpys.ma".
include "basic_2/computation/cpxs_cpxs.ma".

(* SN EXTENDED PARALLEL REDUCTION FOR LOCAL ENVIRONMENTS ********************)

(* Main properties **********************************************************)

axiom cpys_split_down: ∀G,L,T1,T2,d,e. ⦃G, L⦄ ⊢ T1 ▶*×[d, e] T2 →
                       ∀i. d ≤ i → i ≤ d + e →
                       ∃∃T. ⦃G, L⦄ ⊢ T1 ▶*×[i, d+e-i] T & ⦃G, L⦄ ⊢ T ▶*×[d, i-d] T2.

lemma cpys_tpxs_trans: ∀h,g,G,L,T1,T,d,e. ⦃G, L⦄ ⊢ T1 ▶*×[d, e] T →
                       ∀T2. ⦃G, ⋆⦄ ⊢ T ➡*[h, g] T2 → ⦃G, L⦄ ⊢ T1 ➡*[h, g] T2.
#h #g #G #L #T1 #T #d #e #HT1 #T2 #H @(cpxs_ind … H) -T2
/3 width=5 by cpxs_strap1, cpys_cpx, lsubr_cpx_trans, cpx_cpxs/
qed-.

lemma cpx_fwd_cpys_tpxs: ∀h,g,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡[h, g] T2 →
                         ∃∃T. ⦃G, L⦄ ⊢ T1 ▶*×[0, ∞] T & ⦃G, ⋆⦄ ⊢ T ➡*[h, g] T2.
#h #g #G #L #T1 #T2 #H elim H -G -L -T1 -T2
[ /2 width=3 by ex2_intro/
| /4 width=3 by cpx_cpxs, cpx_sort, ex2_intro/
| #I #G #L #K #V1 #V2 #W2 #i #HLK #_ #HVW2 * #V #HV1 #HV2
  elim (lift_total V 0 (i+1)) #W #HVW
  lapply (cpxs_lift … HV2 (⋆) (Ⓣ) … HVW … HVW2)
  [ @ldrop_atom #H destruct | /3 width=7 by cpys_subst_Y2, ex2_intro/ ]
| #a #I #G #L #V1 #V2 #T1 #T2 #_ #_ * #V #HV1 #HV2 * #T #HT1 #HT2
  @(ex2_intro … (ⓑ{a,I}V1.T))
  [ @cpys_bind //
  | @cpxs_bind //
  
  elim (cpys_split_down … HT1 1) -HT1 // #T0 #HT10 #HT0
  @(ex2_intro … (ⓑ{a,I}V.T0))
  [ @cpys_bind //
  | @(cpxs_trans … (ⓑ{a,I}V.T)) @cpxs_bind // -HT10


(*  
  lapply (lsuby_cpys_trans … HT10 (L.ⓑ{I}V) ?) -HT10 /2 width=1 by lsuby_succ/ #HT10
*)
| #I #G #L #V1 #V2 #T1 #T2 #_ #_ * #V #HV1 #HV2 *
  /3 width=5 by cpys_flat, cpxs_flat, ex2_intro/