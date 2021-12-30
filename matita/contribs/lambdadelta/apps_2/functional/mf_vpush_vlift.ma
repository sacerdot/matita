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
include "apps_2/functional/mf_vpush.ma".

(* MULTIPLE FILLING PUSH ****************************************************)

(* Properties with multiple filling lift ************************************)

lemma mf_vpush_vlift_swap_O (v) (T) (l): ⇡[0←↑[↑l,1]T]⇡[l]v ⊜⇡[↑l]⇡[0←T]v.
#v #T #l #i
elim (eq_or_gt i) #Hi destruct
[ >mf_vpush_eq >mf_vlift_rw >mf_vpush_eq //
| >(mf_vpush_gt … Hi) >mf_vlift_rw >mf_vlift_rw >(mf_vpush_gt … Hi)
  @mf_vlift_swap //
]
qed.

lemma mf_vpush_vlift_swap_O_lref_O (v) (l): ⇡[0←#0]⇡[l]v ⊜⇡[↑l]⇡[0←#0]v.
#v #l @(mf_vpush_vlift_swap_O … (#0))
qed.
