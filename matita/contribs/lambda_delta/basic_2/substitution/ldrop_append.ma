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

include "basic_2/grammar/lenv_append.ma".
include "basic_2/substitution/ldrop.ma".

(* DROPPING *****************************************************************)

(* Properties on append for local environments ******************************)

lemma ldrop_append_O1_ge: ∀K,L1,L2,e. ⇩[0, e] L1 @@ L2 ≡ K →
                          |L2| ≤ e → ⇩[0, e - |L2|] L1 ≡ K.
#K #L1 #L2 elim L2 -L2 normalize //
#L2 #I #V #IHL2 #e #H #H1e
elim (ldrop_inv_O1 … H) -H * #H2e #HL12 destruct
[ lapply (le_n_O_to_eq … H1e) -H1e -IHL2
  >commutative_plus normalize #H destruct
| <minus_plus >minus_minus_comm /3 width=1/
]
qed.

lemma ldrop_append_O1_lt: ∀K,L1,L2,e. ⇩[0, e] L1 @@ L2 ≡ K → e < |L2| →
                          ∃∃K2. ⇩[0, e] L2 ≡ K2 & K = L1 @@ K2.
#K #L1 #L2 elim L2 -L2
[ #e #_ #H elim (lt_zero_false … H)
| #L2 #I #V #IHL2 #e normalize #HL12 #H1e
  elim (ldrop_inv_O1 … HL12) -HL12 * #H2e #HL12 destruct
  [ -H1e -IHL2 /3 width=3/
  | elim (IHL2 … HL12 ?) -IHL2 -HL12 /2 width=1/ -H1e #K2 #HLK2 #H destruct /3 width=3/
  ]
]
qed.
