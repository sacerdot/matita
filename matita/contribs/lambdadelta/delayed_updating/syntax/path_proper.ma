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
include "delayed_updating/notation/relations/predicate_p_tail_1.ma".
include "ground/xoa/ex_1_2.ma".

(* PROPER CONDITION FOR PATH ************************************************)

definition ppc: predicate path ≝
           λp. 𝐞 = p → ⊥
.

interpretation
  "proper condition (path)"
  'PredicatePTail p = (ppc p).

(* Basic constructions ******************************************************)

lemma ppc_lcons (l) (q): Ꝕ(l◗q).
#l #p #H destruct
qed.

(* Basic inversions ********************************************************)

lemma ppc_inv_lcons (p):
      Ꝕp → ∃∃l,q. l◗q = p.
*
[ #H elim H -H //
| #l #q #_ /2 width=3 by ex1_2_intro/
]
qed-.
