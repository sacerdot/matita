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

include "apps_2/functional/mf_vlift_exteq.ma".
include "apps_2/functional/mf_vpush_exteq.ma".
include "apps_2/functional/mf.ma".

(* MULTIPLE FILLING FOR TERMS ***********************************************)

(* Properties with extensional equivalence **********************************)

lemma mf_comp (T): compatible_3 … (λgv,lv.●[gv,lv]T) (exteq …) (exteq …) (eq …).
#T elim T -T *
[ //
| #i #gv1 #gv2 #Hgv #lv1 #lv2 #Hlv
  whd in ⊢ (??%%); //
| #i #gv1 #gv2 #Hgv #lv1 #lv2 #Hlv
  whd in ⊢ (??%%); //
| #p #I #V #T #IHV #IHT #gv1 #gv2 #Hgv #lv1 #lv2 #Hlv
  whd in ⊢ (??%%); /4 width=1 by mf_vlift_comp, mf_vpush_comp, eq_f3/
| #I #V #T #IHV #IHT #gv1 #gv2 #Hgv #lv1 #lv2 #Hlv
  whd in ⊢ (??%%); /3 width=1 by eq_f3/
]
qed-.

(* Advanced properties ******************************************************)

lemma mf_id (T): ●[mf_gi,mf_li]T = T.
#T elim T -T * //
[ #p #I #V #T #IHV #IHT
  <IHV in ⊢ (???%); <IHT in ⊢ (???%); -IHV -IHT
  whd in ⊢ (??%?); /3 width=1 by mf_comp, eq_f3/
| #I #V #T #IHV #IHT
  <IHV in ⊢ (???%); <IHT in ⊢ (???%); -IHV -IHT //
]
qed.
