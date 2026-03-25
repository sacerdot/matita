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

include "ground/xoa/ex_2_4.ma".
include "delayed_updating/syntax/prototerm_eq.ma".
include "delayed_updating/substitution/fsubst.ma".
include "delayed_updating/reduction/prototerm_cx_redex.ma".
include "delayed_updating/reduction/prototerm_x_focus.ma".
include "delayed_updating/reduction/prototerm_immediate.ma".
include "delayed_updating/notation/relations/black_rightarrow_ibf_3.ma".

(* IMMEDIATE BALANCED FOCUSED REDUCTION *************************************)

definition ibfs (r): relation2 (𝕋) (𝕋) ≝
           λt1,t2.
           ∃∃p,b,q,n. r ϵ 𝐑❨t1,p,b,q,n❩ &
           ⬕[𝐅❨p,b,q,n❩←𝐈❨t1,p,b,q,n❩]t1 ⇔ t2
.

interpretation
  "balanced focused reduction with immediate updating (prototerm)"
  'BlackRightArrowIBF t1 r t2 = (ibfs r t1 t2).

(* Basic constructions ******************************************************)

lemma ibfs_mk (t1) (t2) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨t1,p,b,q,n❩ →
      ⬕[𝐅❨p,b,q,n❩←𝐈❨t1,p,b,q,n❩]t1 ⇔ t2 →
      t1 ➡𝐢𝐛𝐟[r] t2.
#t1 #t2 #r #p #b #q #n #Hr #Ht12
@(ex2_4_intro … Hr Ht12)
qed.

lemma pcxr_ibfs (t1) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨t1,p,b,q,n❩ →
      ∃t2. t1 ➡𝐢𝐛𝐟[r] t2.
#t1 #r #p #b #q #n #Hr
lapply (pcxr_des_n … Hr) #Hn
@ex_intro [| @(ibfs_mk … Hr) @subset_eq_refl ]
qed-.

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

(* Advanced destructions ****************************************************)

lemma ibfs_des_r (t1) (t2) (r):
      t1 ➡𝐢𝐛𝐟[r] t2 → r ϵ t1.
#t1 #t2 #r * #p #b #q #n #Hr #_
lapply (pcxr_des_r … Hr) #H0 destruct
/2 width=2 by pcxr_des_n/
qed-.
