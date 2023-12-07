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

include "delayed_updating/unwind/unwind2_preterm_ol.ma".
include "delayed_updating/unwind/unwind2_preterm.ma".
include "delayed_updating/unwind/unwind2_prototerm_ol.ma".
include "delayed_updating/unwind/unwind2_prototerm_eq.ma".
include "delayed_updating/substitution/fsubst.ma".

(* TAILED UNWIND FOR PRETERM ************************************************)

(* Constructions with fsubst ************************************************)

lemma unwind2_term_fsubst_sn (f) (t) (u1) (u2):
      t ∪ u1 ϵ 𝐓 →
      ⬕[▼[f]u1←▼[f]u2]▼[f]t ⊆ ▼[f]⬕[u1←u2]t.
#f #t #u1 #u2 #Htu1 #r * *
[ /4 width=3 by term_ol_inv_unwind_bi, unwind2_term_le_repl_dx, fsubst_in_comp_true/
| * #s #Hs #H1 #H0 destruct
  /5 width=1 by fsubst_in_comp_false, in_comp_unwind2_bi/
]
qed-.

lemma unwind2_term_fsubst_dx (f) (t) (u1) (u2):
      t ∪ u1 ϵ 𝐓 →
      ▼[f]⬕[u1←u2]t ⊆ ⬕[▼[f]u1←▼[f]u2]▼[f]t.
#f #t #u1 #u2 #Ht #r * #s * *
[ #H0 #Hs #H1 destruct
  /3 width=1 by fsubst_in_comp_true, term_ol_unwind2_bi, in_comp_unwind2_bi/
| #Hs #H0 #H1 destruct
  /4 width=3 by fsubst_in_comp_false, in_comp_inv_unwind2_bi, in_comp_unwind2_bi/
]
qed-.

lemma unwind2_term_fsubst (f) (t) (u1) (u2):
      t ∪ u1 ϵ 𝐓 →
      ⬕[▼[f]u1←▼[f]u2]▼[f]t ⇔ ▼[f]⬕[u1←u2]t.
/3 width=1 by unwind2_term_fsubst_sn, unwind2_term_fsubst_dx, conj/ qed.
