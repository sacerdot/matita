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

include "delayed_updating/syntax/path.ma".
include "delayed_updating/notation/functions/class_p_0.ma".
include "ground/lib/subset.ma".
include "ground/xoa/ex_1_2.ma".

(* PROPER CONDITION FOR PATH ************************************************)

definition ppc: predicate path ≝
           λp. 𝐞 = p → ⊥
.

interpretation
  "proper condition (path)"
  'ClassP = (ppc).

(* Basic constructions ******************************************************)

lemma ppc_lcons (l) (q): l◗q ϵ 𝐏.
#l #q #H0 destruct
qed.

lemma ppc_rcons (l) (q): q◖l ϵ 𝐏.
#l #q #H
elim (eq_inv_list_empty_rcons ??? H)
qed.

(* Basic inversions ********************************************************)

lemma ppc_inv_empty:
      (𝐞) ϵ 𝐏 → ⊥.
#H0 @H0 -H0 //
qed-.

lemma ppc_inv_lcons (p):
      p ϵ 𝐏 → ∃∃l,q. l◗q = p.
*
[ #H0 elim (ppc_inv_empty … H0)
| #l #q #_ /2 width=3 by ex1_2_intro/
]
qed-.

lemma ppc_inv_rcons (p):
      p ϵ 𝐏 → ∃∃q,l. q◖l = p.
#p @(list_ind_rcons … p) -p
[ #H0 elim (ppc_inv_empty … H0)
| #q #l #_ #_ /2 width=3 by ex1_2_intro/
]
qed-.
