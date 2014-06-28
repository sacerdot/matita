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
include "basic_2/substitution/drop.ma".

(* DROPPING *****************************************************************)

(* Properties on append for local environments ******************************)

fact drop_O1_append_sn_le_aux: ∀L1,L2,s,d,e. ⇩[s, d, e] L1 ≡ L2 →
                               d = 0 → e ≤ |L1| →
                               ∀L. ⇩[s, 0, e] L @@ L1 ≡ L @@ L2.
#L1 #L2 #s #d #e #H elim H -L1 -L2 -d -e normalize
[2,3,4: /4 width=1 by drop_skip_lt, drop_drop, arith_b1, lt_minus_to_plus_r, monotonic_pred/ ]
#d #e #_ #_ #H <(le_n_O_to_eq … H) -H //
qed-.

lemma drop_O1_append_sn_le: ∀L1,L2,s,e. ⇩[s, 0, e] L1 ≡ L2 → e ≤ |L1| →
                            ∀L. ⇩[s, 0, e] L @@ L1 ≡ L @@ L2.
/2 width=3 by drop_O1_append_sn_le_aux/ qed.

(* Inversion lemmas on append for local environments ************************)

lemma drop_O1_inv_append1_ge: ∀K,L1,L2,s,e. ⇩[s, 0, e] L1 @@ L2 ≡ K →
                              |L2| ≤ e → ⇩[s, 0, e - |L2|] L1 ≡ K.
#K #L1 #L2 elim L2 -L2 normalize //
#L2 #I #V #IHL2 #s #e #H #H1e
elim (drop_inv_O1_pair1 … H) -H * #H2e #HL12 destruct
[ lapply (le_n_O_to_eq … H1e) -H1e -IHL2
  >commutative_plus normalize #H destruct
| <minus_plus >minus_minus_comm /3 width=1 by monotonic_pred/
]
qed-.

lemma drop_O1_inv_append1_le: ∀K,L1,L2,s,e. ⇩[s, 0, e] L1 @@ L2 ≡ K → e ≤ |L2| →
                              ∀K2. ⇩[s, 0, e] L2 ≡ K2 → K = L1 @@ K2.
#K #L1 #L2 elim L2 -L2 normalize
[ #s #e #H1 #H2 #K2 #H3 lapply (le_n_O_to_eq … H2) -H2
  #H2 elim (drop_inv_atom1 … H3) -H3 #H3 #_ destruct
  >(drop_inv_O2 … H1) -H1 //
| #L2 #I #V #IHL2 #s #e @(nat_ind_plus … e) -e [ -IHL2 ]
  [ #H1 #_ #K2 #H2
    lapply (drop_inv_O2 … H1) -H1 #H1
    lapply (drop_inv_O2 … H2) -H2 #H2 destruct //
  | /4 width=7 by drop_inv_drop1, le_plus_to_le_r/
  ]
]
qed-.
