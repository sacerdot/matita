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

include "basic_2A/multiple/drops.ma".
include "basic_2A/static/aaa_lift.ma".

(* ATONIC ARITY ASSIGNMENT ON TERMS *****************************************)

(* Properties concerning generic relocation *********************************)

lemma aaa_lifts: ∀G,L1,L2,T2,A,s,cs. ⬇*[s, cs] L2 ≡ L1 → ∀T1. ⬆*[cs] T1 ≡ T2 →
                 ⦃G, L1⦄ ⊢ T1 ⁝ A → ⦃G, L2⦄ ⊢ T2 ⁝ A.
#G #L1 #L2 #T2 #A #s #cs #H elim H -L1 -L2 -cs
[ #L #T1 #H #HT1
  <(lifts_inv_nil … H) -H //
| #L1 #L #L2 #cs #l #m #_ #HL2 #IHL1 #T1 #H #HT1
  elim (lifts_inv_cons … H) -H /3 width=10 by aaa_lift/
]
qed.
