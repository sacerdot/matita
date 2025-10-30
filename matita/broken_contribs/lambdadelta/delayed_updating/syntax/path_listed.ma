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

include "ground/subsets/subset_listed.ma".
include "delayed_updating/syntax/path.ma".

(* Constructions with subset_listed *****************************************)

lemma in_path_append_sx_listed (p) (rs1):
      ∃rs2. ∀q. q ϵ 𝐗❨rs1❩ → p●q ϵ 𝐗❨rs2❩.
#p #rs1 elim rs1 -rs1
[ @(ex_intro … (ⓔ)) #q #H0
  elim (subset_nin_inv_empty ?? H0)
| #r1 #rs1 * #rs2 #Hrs2
  @(ex_intro … ((p●r1)⨮rs2)) #q #H0
  elim (subset_in_inv_listed_lcons ???? H0) -H0 #H0 destruct
  /3 width=1 by subset_in_listed_lcons_dx/
]
qed-.

(* Inversions with subset_listed ********************************************)

lemma in_inv_path_append_sx_listed (p) (rs2):
      ∃rs1. ∀q. p●q ϵ 𝐗❨rs2❩ → q ϵ 𝐗❨rs1❩.
#p #rs2 elim rs2 -rs2
[ @(ex_intro … (ⓔ)) #q #H0
  elim (subset_nin_inv_empty ?? H0)
| #r2 #rs2 * #rs1 #Hrs1
  elim (is_path_append_sx_dec p r2) [ * #s #H0 destruct | #Hnq ]
  [ @(ex_intro … (s⨮rs1)) #q #H0
    elim (subset_in_inv_listed_lcons ???? H0) -H0 #H0
    [ lapply (eq_inv_list_append_dx_bi … H0) -H0 #H0 destruct //
    | /3 width=1 by subset_in_listed_lcons_dx/
    ]
  | @(ex_intro … rs1) #q #H0
    elim (subset_in_inv_listed_lcons ???? H0) -H0 #H0 destruct
    [ elim Hnq -Hnq -rs1 -rs2 /2 width=2 by ex_intro/
    | /2 width=1 by/
    ]
  ]
]
qed-.
