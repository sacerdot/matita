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
include "ground_2/notation/functions/downspoon_2.ma".
include "apps_2/notation/models/downspoon_3.ma".
include "apps_2/models/model.ma".

(* EVALUATION DROP **********************************************************)

definition vdrop (M): nat → evaluation M → evaluation M ≝
                      λj,lv,i. tri … i j (lv i) (lv (↑i)) (lv (↑i)).

interpretation "generic drop (model evaluation)"
   'DownSpoon M i lv = (vdrop M i lv).

interpretation "drop (model evaluation)"
   'DownSpoon M lv = (vdrop M O lv).

(* Basic properties *********************************************************)

lemma vdrop_lt (M): ∀lv,j,i. i < j → (⫰{M}[j] lv) i = lv i.
/2 width=1 by tri_lt/ qed-.

lemma vdrop_ge (M): ∀lv,j,i. j ≤ i → (⫰{M}[j] lv) i = lv (↑i).
#M #lv #j #i #Hji elim (le_to_or_lt_eq … Hji) -Hji #Hji destruct
[ /2 width=1 by tri_gt/
| /2 width=1 by tri_eq/
]
qed-.

lemma vdrop_ext (M): ∀i. compatible_2 … (vdrop M i) (exteq …) (exteq …).
#M #i #lv1 #lv2 #Hlv12 #j elim (lt_or_ge j i) #Hji
[ >vdrop_lt // >vdrop_lt //
| >vdrop_ge // >vdrop_ge //
]
qed.
