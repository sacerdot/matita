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

include "basic_2/substitution/ldrop.ma".

(* DROPPING *****************************************************************)

(* Properties on append for local environments ******************************)

fact ldrop_O1_append_sn_le_aux: ∀L1,L2,d,e. ⇩[d, e] L1 ≡ L2 →
                                d = 0 → e ≤ |L1| →
                                ∀L. ⇩[0, e] L @@ L1 ≡ L @@ L2.
#L1 #L2 #d #e #H elim H -L1 -L2 -d -e normalize // /4 width=1/
#d #e #_ #H #L -d
lapply (le_n_O_to_eq … H) -H //
qed-.

lemma ldrop_O1_append_sn_le: ∀L1,L2,e. ⇩[0, e] L1 ≡ L2 → e ≤ |L1| →
                             ∀L. ⇩[0, e] L @@ L1 ≡ L @@ L2.
/2 width=3 by ldrop_O1_append_sn_le_aux/ qed.

(* Inversion lemmas on append for local environments ************************)

lemma ldrop_O1_inv_append1_ge: ∀K,L1,L2,e. ⇩[0, e] L1 @@ L2 ≡ K →
                               |L2| ≤ e → ⇩[0, e - |L2|] L1 ≡ K.
#K #L1 #L2 elim L2 -L2 normalize //
#L2 #I #V #IHL2 #e #H #H1e
elim (ldrop_inv_O1 … H) -H * #H2e #HL12 destruct
[ lapply (le_n_O_to_eq … H1e) -H1e -IHL2
  >commutative_plus normalize #H destruct
| <minus_plus >minus_minus_comm /3 width=1/
]
qed-.

lemma ldrop_O1_inv_append1_le: ∀K,L1,L2,e. ⇩[0, e] L1 @@ L2 ≡ K → e ≤ |L2| →
                               ∀K2. ⇩[0, e] L2 ≡ K2 → K = L1 @@ K2.
#K #L1 #L2 elim L2 -L2 normalize
[ #e #H1 #H2 #K2 #H3
  lapply (le_n_O_to_eq … H2) -H2 #H2
  lapply (ldrop_inv_atom1 … H3) -H3 #H3 destruct
  >(ldrop_inv_refl … H1) -H1 //
| #L2 #I #V #IHL2 #e @(nat_ind_plus … e) -e [ -IHL2 ]
  [ #H1 #_ #K2 #H2
    lapply (ldrop_inv_refl … H1) -H1 #H1
    lapply (ldrop_inv_refl … H2) -H2 #H2 destruct //
  | #e #_ #H1 #H #K2 #H2
    lapply (le_plus_to_le_r … H) -H
    lapply (ldrop_inv_ldrop1 … H1 ?) -H1 //
    lapply (ldrop_inv_ldrop1 … H2 ?) -H2 //
    <minus_plus_m_m /2 width=4/
  ]
]
qed-.
