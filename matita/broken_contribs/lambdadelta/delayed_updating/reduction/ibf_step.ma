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

include "ground/relocation/fb/fbr_uni.ma".
include "ground/xoa/ex_2_4.ma".
include "delayed_updating/syntax/path_depth.ma".
include "delayed_updating/syntax/prototerm_eq.ma".
include "delayed_updating/syntax/prototerm_clear.ma".
include "delayed_updating/substitution/lift_prototerm.ma".
include "delayed_updating/substitution/fsubst.ma".
include "delayed_updating/reduction/prototerm_reducible.ma".
include "delayed_updating/reduction/prototerm_focus.ma".
include "delayed_updating/notation/relations/black_rightarrow_ibf_3.ma".

(* IMMEDIATE BALANCED FOCUSED REDUCTION *************************************)

definition ibfs (r): relation2 (𝕋) (𝕋) ≝
           λt1,t2.
           ∃∃p,b,q,n. r ϵ 𝐑❨t1,p,b,q,n❩ &
           ⬕[𝐅❨p,b,q❩←(p●𝗔◗(⓪b)●𝗟◗q)●🠡[𝐮❨⁤↑(♭b+n)❩]⋔[p◖𝗦]t1]t1 ⇔ t2
.

interpretation
  "balanced focused reduction with immediate updating (prototerm)"
  'BlackRightArrowIBF t1 r t2 = (ibfs r t1 t2).

(* Basic constructions ******************************************************)

lemma ibfs_mk (t1) (t2) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨t1,p,b,q,n❩ →
      ⬕[𝐅❨p,b,q❩←(p●𝗔◗(⓪b)●𝗟◗q)●🠡[𝐮❨⁤↑(♭b+n)❩]⋔[p◖𝗦]t1]t1 ⇔ t2 →
      t1 ➡𝐢𝐛𝐟[r] t2.
#t1 #t2 #r #p #b #q #n #Hr #Ht12
@(ex2_4_intro … Hr Ht12)
qed.

(* Constructions with subset_equivalence ************************************)

lemma ibfs_eq_trans (t) (t1) (t2) (r):
      t1 ➡𝐢𝐛𝐟[r] t → t ⇔ t2 → t1 ➡𝐢𝐛𝐟[r] t2.
#t #t1 #t2 #r
* #p #b #q #n #Hr #Ht1 #Ht2
@(ibfs_mk … Hr) -Hr
@(subset_eq_trans … Ht1) -Ht1 //
qed-.

lemma dbfs_eq_canc_dx (t) (t1) (t2) (r):
      t1 ➡𝐢𝐛𝐟[r] t → t2 ⇔ t → t1 ➡𝐢𝐛𝐟[r] t2.
/3 width=3 by ibfs_eq_trans, subset_eq_sym/
qed-.

(* Basic destructions *******************************************************)

lemma ibfs_des_in_comp_neq (t1) (t2) (r) (s):
      t1 ➡𝐢𝐛𝐟[r] t2 → ⓪s ⧸ϵ ↑r →
      s ϵ t1 → s ϵ t2.
#t1 #t2 #r #s *
#p #b #q #n #Hr #Ht12 #Hns #Hs
lapply (xprc_des_r … Hr) -Hr #H0 destruct
@(subset_in_eq_repl_fwd ????? Ht12) -t2
/4 width=1 by fsubst_in_comp_false, term_slice_clear/
qed-.
