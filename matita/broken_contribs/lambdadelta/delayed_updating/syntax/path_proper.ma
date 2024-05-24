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

include "ground/notation/functions/subset_p_0.ma".
include "ground/xoa/ex_1_2.ma".
include "ground/subsets/subset.ma".
include "delayed_updating/syntax/path.ma".

(* PROPER CONDITION FOR PATH ************************************************)

definition ppc: 𝒫❨ℙ❩ ≝
           {p | 𝐞 ⧸= p}
.

interpretation
  "proper condition (path)"
  'SubsetP = (ppc).

(* Basic constructions ******************************************************)

lemma ppc_rcons (p) (l):
      p◖l ϵ 𝐏.
#p #l #H0 destruct
qed.

lemma ppc_lcons (p) (l):
      l◗p ϵ 𝐏.
#p #l #H0
elim (eq_inv_list_empty_rcons ??? H0)
qed.

(* Basic inversions ********************************************************)

lemma ppc_inv_empty:
      (𝐞) ⧸ϵ 𝐏 .
#H0 @H0 -H0 //
qed-.

lemma ppc_inv_rcons (p):
      p ϵ 𝐏 → ∃∃q,l. q◖l = p.
*
[ #H0 elim (ppc_inv_empty … H0)
| #l #q #_ /2 width=3 by ex1_2_intro/
]
qed-.

lemma ppc_inv_lcons (p):
      p ϵ 𝐏 → ∃∃q,l. l◗q = p.
#p @(list_ind_rcons … p) -p
[ #H0 elim (ppc_inv_empty … H0)
| #q #l #_ #_ /2 width=3 by ex1_2_intro/
]
qed-.

lemma path_inv_ppc (p):
      ∨∨ 𝐞 = p | p ϵ 𝐏.
*
[ /2 width=1 by or_introl/
| /3 width=3 by ppc_rcons, or_intror/
]
qed-.

(* Advanced constructions ***************************************************)

lemma in_comp_ppc_append_sn (p) (q):
      p ϵ 𝐏 → p●q ϵ 𝐏.
#p #q #Hp #H0
elim (eq_inv_list_empty_append … H0) -H0 #_ #H0 destruct
/2 width=1 by ppc_inv_empty/
qed.
