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

include "ground/arith/nat_le.ma".
include "ground/lib/list_length.ma".
include "ground/subsets/subset_nimply_ol_le.ma".
include "ground/subsets/subset_nimply_or_eq.ma".
include "ground/subsets/subset_listed_or_eq.ma".
include "ground/subsets/subset_listed_nimply.ma".
include "ground/subsets/subset_listed_nimply_le.ma".

(* SUBSET WITH LISTED ELEMENTS **********************************************)

(* Constructions with subset_eq *********************************************)

lemma subset_listed_dx_le_to_eq (A:Type[0]):
      (∀a1,a2. Decidable … (a1 ={A} a2)) →
      ∀l2,u. (∀a. Decidable (a ϵ{A} u)) → u ⊆ 𝐗❨l2❩ →
      ∃∃l1. u ⇔ 𝐗❨l1❩ & ❘l1❘ ≤ ❘l2❘.
#A #HA #l2 elim l2 -l2 [| #a2 #l2 #IH ] #u #Hu #Hl2
[ @(ex2_intro … (ⓔ)) -Hu
  /3 width=1 by subset_empty_le_sn, conj/
| lapply (subset_le_inv_listed_lcons_dx ???? Hl2) -Hl2 #Hl2
  elim (Hu a2) #Ha2
  [ elim (IH … Hl2) -IH -Hl2 [ #l1 #H1l1 #H2l1 ]
    [ lapply (subset_eq_or_dx … H1l1) -H1l1
      [ /2 width=1 by subset_in_listed_dec/
      | /2 width=3 by subset_single_le_sn/
      ] #H1l1
      lapply (subset_eq_trans … H1l1 … (subset_eq_or_listed_lcons …)) -H1l1 #h1l1
      /3 width=4 by nle_succ_bi, ex2_intro/
    | /2 width=1 by in_nimp_single_dx_dec/
    ]
  | lapply (subset_le_trans A ?? (subset_le_nimp_dx_refl_sn_fwd …) … Hl2) -Hl2
    [ * #x2 #Hx2 #H0
      lapply (subset_in_inv_single ??? H0) -H0 #H0 destruct
      /2 width=1 by/
    ] -Ha2 #Hl2
    elim (IH … Hu Hl2) -IH -Hu -Hl2 #l1 #H1l1 #H2l1
    /3 width=3 by nle_succ_dx, ex2_intro/
  ]
]
qed-.
