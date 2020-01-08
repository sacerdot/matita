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

include "static_2/syntax/acle.ma".
include "basic_2/dynamic/cnv_aaa.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

(* Properties with preorder for applicability domains ***********************)

lemma cnv_acle_trans (h) (a1) (a2):
      a1 ⊆ a2 → ∀G,L,T. ❪G,L❫ ⊢ T ![h,a1] → ❪G,L❫ ⊢ T ![h,a2].
#h #a1 #a2 #Ha12 #G #L #T #H elim H -G -L -T
[ /1 width=1 by cnv_sort/
| /3 width=1 by cnv_zero/
| /3 width=1 by cnv_lref/
| /3 width=1 by cnv_bind/
| #n1 #p #G #L #V #W #T #U #Hn1 #_ #_ #HVW #HTU #IHV #IHT
  elim (Ha12 … Hn1) -a1 #n2 #Hn2 #Hn12
  /3 width=11 by cnv_appl_ge/
| /3 width=3 by cnv_cast/
]
qed-.

lemma cnv_acle_omega (h) (a):
      ∀G,L,T. ❪G,L❫ ⊢ T ![h,a] → ❪G,L❫ ⊢ T ![h,𝛚].
/3 width=3 by cnv_acle_trans, acle_omega/ qed-.

lemma cnv_acle_one (h) (a) (n):
      ∀G,L,T. ❪G,L❫ ⊢ T ![h,𝟏] → ad a n → ❪G,L❫ ⊢ T ![h,a].
/3 width=3 by cnv_acle_trans, acle_one/ qed-.
