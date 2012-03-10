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

include "Basic_2/unfold/ldrops.ma".
include "Basic_2/static/aaa_lift.ma".

(* ATONIC ARITY ASSIGNMENT ON TERMS *****************************************)

(* Properties concerning generic relocation *********************************)

lemma aaa_lifts: ∀L1,L2,T2,A,des. ⇩*[des] L2 ≡ L1 → ∀T1. ⇧*[des] T1 ≡ T2 →
                                  L1 ⊢ T1 ÷ A →  L2 ⊢ T2 ÷ A.
#L1 #L2 #T2 #A #des #H elim H -L1 -L2 -des
[ #L #T1 #H #HT1
  <(lifts_inv_nil … H) -H //
| #L1 #L #L2 #des #d #e #_ #HL2 #IHL1 #T1 #H #HT1
  elim (lifts_inv_cons … H) -H /3 width=9/
]
qed.
