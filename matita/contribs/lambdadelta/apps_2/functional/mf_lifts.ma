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

include "apps_2/functional/mf_vpush_vlift.ma".
include "apps_2/functional/mf_exteq.ma".

(* MULTIPLE FILLING FOR TERMS ***********************************************)

(* Properties with relocation ***********************************************)

lemma mf_lifts_basic_SO_dx (T) (j): ∀gv,lv. ↑[j,1]■[gv,lv]T = ■[⇡[j]gv,⇡[j]lv]T.
#T elim T -T * //
[ #p #I #V #T #IHV #IHT #j #gv #lv
  >mf_bind >mf_bind >flifts_basic_bind
  /4 width=1 by mf_comp, mf_vlift_swap, eq_f2/
| #I #V #T #IHV #IHT #j #gv #lv
  >mf_flat >mf_flat >flifts_flat
  //
]
qed.
