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

include "ground/lib/functions.ma".
include "apps_2/functional/flifts_flifts_basic.ma".
include "apps_2/functional/mf_vpush.ma".

(* MULTIPLE FILLING PUSH ****************************************************)

(* Properties with extensional equivalence **********************************)

lemma mf_lc_id: ⇡[0←#0]mf_li ≐ mf_li.
#i elim (eq_or_gt i) #Hi destruct //
>mf_vpush_gt // >(flifts_lref_uni 1) <(S_pred … Hi) in ⊢ (???%); -Hi //
qed.

lemma mf_vpush_comp (i): compatible_3 … (mf_vpush i) (eq …) (exteq …) (exteq …).
#i #T1 #T2 #HT12 #lv1 #lv2 #Hlv #j
elim (lt_or_eq_or_gt j i) #Hij destruct
[ >mf_vpush_lt // >mf_vpush_lt //
| >mf_vpush_eq >mf_vpush_eq //
| >mf_vpush_gt // >mf_vpush_gt //
]
qed-.

(* Main properties with extensional equivalence *****************************)

theorem mf_vpush_swap: ∀l1,l2. l2 ≤ l1 →
                       ∀v,T1,T2. ⇡[l2←T2]⇡[l1←T1]v ≐ ⇡[↑l1←↑[l2,1]T1]⇡[l2←T2]v.
#l1 #l2 #Hl21 #v #T1 #T2 #i
elim (lt_or_eq_or_gt i l2) #Hl2 destruct
[ lapply (lt_to_le_to_lt … Hl2 Hl21) #Hl1
  >mf_vpush_lt // >mf_vpush_lt // >mf_vpush_lt /2 width=1 by lt_S/ >mf_vpush_lt //
| >mf_vpush_eq >mf_vpush_lt /2 width=1 by monotonic_le_plus_l/
| >mf_vpush_gt // elim (lt_or_eq_or_gt (↓i) l1) #Hl1 destruct
  [ >mf_vpush_lt // >mf_vpush_lt /2 width=1 by lt_minus_to_plus/ >mf_vpush_gt //
  | >mf_vpush_eq <(lt_succ_pred … Hl2) >mf_vpush_eq //
  | lapply (le_to_lt_to_lt … Hl21 Hl1) -Hl2 #Hl2
    >mf_vpush_gt // >mf_vpush_gt /2 width=1 by lt_minus_to_plus_r/ >mf_vpush_gt //
    /2 width=1 by flifts_basic_swap/
  ]
]
qed-.
