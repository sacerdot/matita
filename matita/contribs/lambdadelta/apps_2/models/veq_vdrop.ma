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

include "apps_2/models/vdrop_vlift.ma".
include "apps_2/models/veq.ma".

(* EVALUATION EQUIVALENCE  **************************************************)

(* Properties with evaluation drop ******************************************)

lemma vdrop_comp (M): ∀i. compatible_2 … (vdrop M i) (veq M) (veq M).
#M #i #lv1 #lv2 #Hlv12 #j elim (lt_or_ge j i) #Hji
[ >vdrop_lt // >vdrop_lt //
| >vdrop_ge // >vdrop_ge //
]
qed.

(* Advanced inversion lemmas with evaluation evaluation lift ****************)

lemma veq_inv_vlift_sn (M): ∀lv1,y2,d1,i. ⫯[i←d1]lv1 ≗{M} y2 →
                            ∃∃lv2,d2. lv1 ≗ lv2 & d1 ≗ d2 & ⫯[i←d2]lv2 ≐ y2.
#M #lv1 #y2 #d1 #i #H
@(ex3_2_intro)
[5: @exteq_sym @vlift_vdrop_eq |1,2: skip
| #j elim (lt_or_ge j i) #Hji
  [ lapply (H j) -H >vlift_lt // >vdrop_lt //
  | lapply (H (↑j)) -H >vlift_gt /2 width=1 by monotonic_le_plus_l/ >vdrop_ge //
  ]
| lapply (H i) >vlift_eq //
]
qed-.
