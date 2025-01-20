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

include "delayed_updating/substitution/fsubst.ma".
include "delayed_updating/syntax/prototerm_constructors.ma".
include "delayed_updating/syntax/prototerm_clear.ma".
include "delayed_updating/syntax/prototerm_eq.ma".
include "delayed_updating/syntax/path_closed.ma".
include "delayed_updating/syntax/path_balanced.ma".
include "delayed_updating/syntax/path_structure.ma".
include "delayed_updating/syntax/path_depth.ma".
include "delayed_updating/notation/relations/parallel_black_rightarrow_dbf_3.ma".

(* DELAYED BALANCED FOCUSED PARALLEL REDUCTION ******************************)

inductive dbfpr (t1): 𝕋 → predicate (𝕋) ≝
| dbfpr_refl (t2) (u):
             t1 ⇔ t2 → u ⊆ Ⓕ → dbfpr t1 u t2
| dbfpr_step (t0) (t2) (u) (p) (b) (q) (n):
             let r ≝ p●𝗔◗b●𝗟◗q in
             let s ≝ p●𝗔◗(⓪b)●𝗟◗q in
             ⊗b ϵ 𝐁 → q ϵ 𝐂❨n❩ → r◖𝗱(⁤↑n) ϵ t1 → ⓪r ϵ u →
             ⬕[↑r←s●𝛕(⁤↑(♭b+n)).⋔[p◖𝗦]t0]t0 ⇔ t2 →
             dbfpr t1 (u⧵❴⓪r❵) t0 →
             dbfpr t1 u t2
.

interpretation
  "balanced focused parallel reduction with delayed updating (prototerm)"
  'ParallelBlackRightArrowDBF t1 u t2 = (dbfpr t1 u t2).

(* Constructions with subset_eq *********************************************)

lemma dbfpr_eq_trans (t0) (t1) (u):
      t1 ∥➡𝐝𝐛𝐟[u] t0 → ∀t2. t0 ⇔ t2 → t1 ∥➡𝐝𝐛𝐟[u] t2.
#t0 #t1 #u #H0 elim H0 -t0 -u
[ #t0 #u #Ht10 #Hu #t2 #Ht02
  /3 width=3 by dbfpr_refl, subset_eq_trans/
| #tx #t0 #u #p #b #q #n #Hb #Hq #Ht1 #Hu #Ht0 #_ #IH #t2 #Ht02
  lapply (subset_eq_trans … Ht0 … Ht02) -t0 #Ht2
  @(dbfpr_step … Hb Hq Ht1 Hu Ht2) -t2 -n -Hb -Hu
  /2 width=1 by/
]
qed-.

lemma dbfpr_eq_canc_dx (t0) (t1) (t2) (u):
      t1 ∥➡𝐝𝐛𝐟[u] t0 → t2 ⇔ t0 → t1 ∥➡𝐝𝐛𝐟[u] t2.
/3 width=3 by dbfpr_eq_trans, subset_eq_sym/
qed-.

lemma dbfpr_eq_canc_sn (t0) (t2) (u):
      t0 ∥➡𝐝𝐛𝐟[u] t2 → ∀t1. t0 ⇔ t1 → t1 ∥➡𝐝𝐛𝐟[u] t2.
#t0 #t2 #u #H0 elim H0 -t2 -u
[ #t2 #u #Ht02 #Hu #t1 #Ht01
  /3 width=3 by subset_eq_canc_sn, dbfpr_refl/
| #tx #t2 #u #p #b #q #n #Hb #Hq #Ht0 #Hu #Ht2 #_ #IH #t1 #Ht01
  @(dbfpr_step … Hb Hq … Hu Ht2)
  [ /2 width=3 by subset_in_eq_repl_fwd/
  | /2 width=1 by/
  ]
]
qed-.

lemma eq_dbfpr_trans (t) (t1) (t2) (u):
      t1 ⇔ t → t ∥➡𝐝𝐛𝐟[u] t2 → t1 ∥➡𝐝𝐛𝐟[u] t2.
/3 width=3 by dbfpr_eq_canc_sn, subset_eq_sym/
qed-.
