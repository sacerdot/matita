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
include "delayed_updating/substitution/lift_prototerm.ma".
include "delayed_updating/syntax/prototerm_eq.ma".
include "delayed_updating/syntax/path_closed.ma".
include "delayed_updating/syntax/path_balanced.ma".
include "delayed_updating/syntax/path_clear.ma".
include "delayed_updating/syntax/path_structure.ma".
include "delayed_updating/syntax/path_depth.ma".
include "delayed_updating/notation/relations/black_rightarrow_ibf_3.ma".
include "ground/relocation/fb/fbr_uni.ma".
include "ground/xoa/ex_5_4.ma".

(* IMMEDIATE BALANCED FOCUSED REDUCTION *************************************)

definition ibfr (r): relation2 (𝕋) (𝕋) ≝
           λt1,t2.
           ∃∃p,b,q,n. p●𝗔◗b●𝗟◗q = r &
           ⊗b ϵ 𝐁 & q ϵ 𝐂❨n❩ & r◖𝗱(⁤↑n) ϵ t1 &
           ⬕[r●↑𝐞←(p◖𝗔)●(⓪b)●(𝗟◗q)●🠡[𝐮❨⁤↑(♭b+n)❩]⋔[p◖𝗦]t1]t1 ⇔ t2
.

interpretation
  "balanced focused reduction with immediate updating (prototerm)"
  'BlackRightArrowIBF t1 r t2 = (ibfr r t1 t2).

(* Constructions with subset_equivalence ************************************)

lemma ibfr_eq_trans (t) (t1) (t2) (r):
      t1 ➡𝐢𝐛𝐟[r] t → t ⇔ t2 → t1 ➡𝐢𝐛𝐟[r] t2.
#t #t1 #t2 #r
* #p #b #q #n #Hr #Hb #Hn #Ht1 #Ht #Ht2
/3 width=13 by subset_eq_trans, ex5_4_intro/
qed-.
