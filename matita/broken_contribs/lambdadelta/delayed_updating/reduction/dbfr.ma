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
include "delayed_updating/notation/relations/black_rightarrow_dbf_3.ma".
include "ground/xoa/ex_5_4.ma".

(* DELAYED BALANCED FOCUSED REDUCTION ***************************************)

definition dbfr (r): relation2 (𝕋) (𝕋) ≝
           λt1,t2.
           ∃∃p,b,q,n. ⓪(p●𝗔◗b●𝗟◗q) = r &
           ⊗b ϵ 𝐁 & q ϵ 𝐂❨n❩ & (p●𝗔◗b●𝗟◗q)◖𝗱(⁤↑n) ϵ t1 &
           ⬕[↑(p●𝗔◗b●𝗟◗q)←(p●𝗔◗(⓪b)●𝗟◗q)●𝛕(⁤↑(♭b+n)).⋔[p◖𝗦]t1]t1 ⇔ t2
.

interpretation
  "balanced focused reduction with delayed updating (prototerm)"
  'BlackRightArrowDBF t1 r t2 = (dbfr r t1 t2).

(* Constructions with subset_eq *********************************************)

lemma dbfr_eq_trans (t) (t1) (t2) (r):
      t1 ➡𝐝𝐛𝐟[r] t → t ⇔ t2 → t1 ➡𝐝𝐛𝐟[r] t2.
#t #t1 #t2 #r
* #p #b #q #n #Hr #Hb #Hn #Ht1 #Ht #Ht2
/3 width=13 by subset_eq_trans, ex5_4_intro/
qed-.

lemma dbfr_eq_canc_dx (t) (t1) (t2) (r):
      t1 ➡𝐝𝐛𝐟[r] t → t2 ⇔ t → t1 ➡𝐝𝐛𝐟[r] t2.
/3 width=3 by dbfr_eq_trans, subset_eq_sym/
qed-.

(* Basic destructions *******************************************************)

lemma dbfr_des_in_comp_neq (t1) (t2) (r) (s):
      t1 ➡𝐝𝐛𝐟[r] t2 → ⓪s ⧸ϵ ↑r →
      s ϵ t1 → s ϵ t2.
#t1 #t2 #r #s *
#p #b #q #n #H0 #_ #_ #_ #Ht2 #Hns #Hs destruct
@(subset_in_eq_repl_fwd ????? Ht2) -t2
/4 width=1 by fsubst_in_comp_false, term_slice_clear/
qed-.
