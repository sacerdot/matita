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

fact drop_O1_append_sn_le_aux: ∀L1,L2,s,l,m. ⬇[s, l, m] L1 ≡ L2 →
                               l = yinj 0 → m ≤ |L1| →
                               ∀L. ⬇[s, yinj 0, m] L @@ L1 ≡ L @@ L2.
#L1 #L2 #s #l #m #H elim H -L1 -L2 -l -m //
[ #l #m #_ #_ #H <(le_n_O_to_eq … H) -H //
| normalize /4 width=1 by drop_drop, monotonic_pred/
| #I #L1 #L2 #V1 #V2 #l #m #_ #_ #_ #H elim (ysucc_inv_O_dx … H)
]
qed-.

lemma drop_O1_append_sn_le: ∀L1,L2,s,m. ⬇[s, yinj 0, m] L1 ≡ L2 → m ≤ |L1| →
                            ∀L. ⬇[s, yinj 0, m] L @@ L1 ≡ L @@ L2.
/2 width=3 by drop_O1_append_sn_le_aux/ qed.

(* Inversion lemmas on append for local environments ************************)

lemma drop_O1_inv_append1_ge: ∀K,L1,L2,s,m. ⬇[s, yinj 0, m] L1 @@ L2 ≡ K →
                              |L2| ≤ m → ⬇[s, yinj 0, m - |L2|] L1 ≡ K.
#K #L1 #L2 elim L2 -L2 normalize //
#L2 #I #V #IHL2 #s #m #H #H1m
elim (drop_inv_O1_pair1 … H) -H * #H2m #HL12 destruct
[ lapply (le_n_O_to_eq … H1m) -H1m -IHL2 <plus_n_Sm #H destruct
| <minus_plus >minus_minus_comm /3 width=1 by monotonic_pred/
]
qed-.

lemma drop_O1_inv_append1_le: ∀K,L1,L2,s,m. ⬇[s, yinj 0, m] L1 @@ L2 ≡ K → m ≤ |L2| →
                              ∀K2. ⬇[s, yinj 0, m] L2 ≡ K2 → K = L1 @@ K2.
#K #L1 #L2 elim L2 -L2 normalize
[ #s #m #H1 #H2 #K2 #H3 lapply (le_n_O_to_eq … H2) -H2
  #H2 elim (drop_inv_atom1 … H3) -H3 #H3 #_ destruct
  >(drop_inv_O2 … H1) -H1 //
| #L2 #I #V #IHL2 #s #m @(nat_ind_plus … m) -m [ -IHL2 ]
  [ #H1 #_ #K2 #H2
    lapply (drop_inv_O2 … H1) -H1 #H1
    lapply (drop_inv_O2 … H2) -H2 #H2 destruct //
  | /4 width=7 by drop_inv_drop1, le_plus_to_le_r/
  ]
]
qed-.
