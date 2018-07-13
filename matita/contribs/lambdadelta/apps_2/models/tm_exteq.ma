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

include "ground_2/lib/functions.ma".
include "ground_2/lib/exteq.ma".
include "apps_2/models/tm.ma".

(* TERM MODEL ***************************************************************)

(* Properties with extensional equivalencs of evaluations *******************) 

lemma tm_gc_id: ∀j. ⇡[j]tm_gc ≐ tm_gc.
// qed.

lemma tm_lc_id: ⇡[0←#0]tm_lc ≐ tm_lc.
#i elim (eq_or_gt i) #Hi destruct //
>tm_vpush_gt // >(flifts_lref_uni 1) <(S_pred … Hi) in ⊢ (???%); -Hi //
qed.

lemma tm_vlift_comp (l): compatible_2 … (tm_vlift l) (exteq …) (exteq …).
#l #gv1 #gv2 #Hgv #i
>tm_vlift_rw >tm_vlift_rw //
qed.

lemma tm_vpush_comp (i): compatible_3 … (tm_vpush i) (eq …) (exteq …) (exteq …).
#i #T1 #T2 #HT12 #lv1 #lv2 #Hlv #j
elim (lt_or_eq_or_gt j i) #Hij destruct
[ >tm_vpush_lt // >tm_vpush_lt //
| >tm_vpush_eq >tm_vpush_eq //
| >tm_vpush_gt // >tm_vpush_gt //
]
qed-.

lemma tm_ti_comp (T): compatible_3 … (λgv,lv.tm_ti gv lv T) (exteq …) (exteq …) (eq …).
#T elim T -T *
[ //
| #i #gv1 #gv2 #Hgv #lv1 #lv2 #Hlv
  whd in ⊢ (??%%); //
| #i #gv1 #gv2 #Hgv #lv1 #lv2 #Hlv
  whd in ⊢ (??%%); //
| #p #I #V #T #IHV #IHT #gv1 #gv2 #Hgv #lv1 #lv2 #Hlv
  whd in ⊢ (??%%); /4 width=1 by tm_vlift_comp, tm_vpush_comp, eq_f3/
| #I #V #T #IHV #IHT #gv1 #gv2 #Hgv #lv1 #lv2 #Hlv
  whd in ⊢ (??%%); /3 width=1 by eq_f3/
]
qed-.

lemma tm_ti_eq (T): tm_ti tm_gc tm_lc T = T.
#T elim T -T * //
[ #p #I #V #T #IHV #IHT
  <IHV in ⊢ (???%); <IHT in ⊢ (???%); -IHV -IHT
  whd in ⊢ (??%?); /3 width=1 by tm_ti_comp, eq_f3/
| #I #V #T #IHV #IHT
  <IHV in ⊢ (???%); <IHT in ⊢ (???%); -IHV -IHT //
]
qed.
