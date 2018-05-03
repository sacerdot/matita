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
include "apps_2/notation/models/upspoon_4.ma".
include "apps_2/notation/models/upspoon_3.ma".
include "apps_2/models/model.ma".


(* MODEL ********************************************************************)

definition vlift (M): nat → dd M → evaluation M → evaluation M ≝
                      λj,d,lv,i. tri … i j (lv i) d (lv (↓i)).

interpretation "generic lift (model evaluation)"
   'UpSpoon M i d lv = (vlift M i d lv).

interpretation "lift (model evaluation)"
   'UpSpoon M d lv = (vlift M O d lv).

(* Basic properties *********************************************************)

lemma vlift_lt (M): ∀lv,d,j,i. i < j → (⫯{M}[j←d] lv) i = lv i.
/2 width=1 by tri_lt/ qed-.

lemma vlift_eq (M): ∀lv,d,i. (⫯{M}[i←d] lv) i = d.
/2 width=1 by tri_eq/ qed-.

lemma vlift_gt (M): ∀lv,d,j,i. j < i → (⫯{M}[j←d] lv) i = lv (↓i).
/2 width=1 by tri_gt/ qed-.

lemma vlift_ext (M): ∀i. compatible_3 … (vlift M i) (eq …) (exteq …) (exteq …).
#m #i #d1 #d2 #Hd12 #lv1 #lv2 #HLv12 #j
elim (lt_or_eq_or_gt j i) #Hij destruct
[ >vlift_lt // >vlift_lt //
| >vlift_eq >vlift_eq //
| >vlift_gt // >vlift_gt //
]
qed.
