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
#l #p #H destruct
qed.

(* Basic inversions ********************************************************)

lemma ppc_inv_lcons (p):
      p ϵ 𝐏 → ∃∃l,q. l◗q = p.
*
[ #H elim H -H //
| #l #q #_ /2 width=3 by ex1_2_intro/
]
qed-.
