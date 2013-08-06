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

include "basic_2/reduction/cpr_lift.ma".
include "basic_2/computation/cprs.ma".

(* CONTEXT-SENSITIVE PARALLEL COMPUTATION ON TERMS **************************)

(* Advanced properties ******************************************************)

(* Note: apparently this was missing in basic_1 *)
lemma cprs_delta: ∀G,L,K,V,V2,i.
                  ⇩[0, i] L ≡ K.ⓓV → ⦃G, K⦄ ⊢ V ➡* V2 →
                  ∀W2. ⇧[0, i + 1] V2 ≡ W2 → ⦃G, L⦄ ⊢ #i ➡* W2.
#G #L #K #V #V2 #i #HLK #H elim H -V2 [ /3 width=6/ ]
#V1 #V2 #_ #HV12 #IHV1 #W2 #HVW2
lapply (ldrop_fwd_ldrop2 … HLK) -HLK #HLK
elim (lift_total V1 0 (i+1)) /4 width=11 by cpr_lift, cprs_strap1/
qed.

(* Advanced inversion lemmas ************************************************)

(* Basic_1: was: pr3_gen_lref *)
lemma cprs_inv_lref1: ∀G,L,T2,i. ⦃G, L⦄ ⊢ #i ➡* T2 →
                      T2 = #i ∨
                      ∃∃K,V1,T1. ⇩[0, i] L ≡ K. ⓓV1 & ⦃G, K⦄ ⊢ V1 ➡* T1 &
                                 ⇧[0, i + 1] T1 ≡ T2.
#G #L #T2 #i #H @(cprs_ind … H) -T2 /2 width=1/
#T #T2 #_ #HT2 *
[ #H destruct
  elim (cpr_inv_lref1 … HT2) -HT2 /2 width=1/
  * /4 width=6/
| * #K #V1 #T1 #HLK #HVT1 #HT1
  lapply (ldrop_fwd_ldrop2 … HLK) #H0LK
  elim (cpr_inv_lift1 … HT2 … H0LK … HT1) -H0LK -T /4 width=6/
]
qed-.

(* Relocation properties ****************************************************)

(* Basic_1: was: pr3_lift *)
lemma cprs_lift: ∀G. l_liftable (cprs G).
/3 width=9/ qed.

(* Basic_1: was: pr3_gen_lift *)
lemma cprs_inv_lift1: ∀G. l_deliftable_sn (cprs G).
/3 width=5 by l_deliftable_sn_LTC, cpr_inv_lift1/
qed-.
