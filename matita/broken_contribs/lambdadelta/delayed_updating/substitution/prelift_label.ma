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

include "delayed_updating/notation/functions/uptrianglearrow_2.ma".
include "delayed_updating/syntax/label.ma".
include "ground/relocation/fb/fbr_coafter.ma".
include "ground/relocation/fb/fbr_dapp_lt.ma".

(* PRELIFT FOR LABEL ********************************************************)

definition prelift_label (f) (l): label ≝
match l with
[ label_d k ⇒ 𝗱(f＠⧣❨k❩)
| label_m   ⇒ 𝗺
| label_z F ⇒ 𝘇(f~•F)
| label_L   ⇒ 𝗟
| label_A   ⇒ 𝗔
| label_S   ⇒ 𝗦
].

interpretation
  "prelift (label)"
  'UpTriangleArrow f l = (prelift_label f l).

(* Basic constructions ******************************************************)

lemma prelift_label_d (f) (k):
      (𝗱(f＠⧣❨k❩)) = 🠡[f]𝗱k.
// qed.

lemma prelift_label_m (f):
      (𝗺) = 🠡[f]𝗺.
// qed.

lemma prelift_label_z (f) (F):
      (𝘇(f~•F)) = 🠡[f]𝘇F.
// qed.

lemma prelift_label_L (f):
      (𝗟) = 🠡[f]𝗟.
// qed.

lemma prelift_label_A (f):
      (𝗔) = 🠡[f]𝗔.
// qed.

lemma prelift_label_S (f):
      (𝗦) = 🠡[f]𝗦.
// qed.

(* Advanced constructions ***************************************************)

lemma prelift_label_id (l):
      l = 🠡[𝐢]l.
* [ #k || #F ] //
qed.

(* Basic inversions *********************************************************)

lemma prelift_label_inv_d_sn (f) (l) (k1):
      (𝗱k1) = 🠡[f]l →
      ∃∃k2. k1 = f＠⧣❨k2❩ & 𝗱k2 = l.
#f * [ #k || #F ] #k1
[ <prelift_label_d
| <prelift_label_m
| <prelift_label_z
| <prelift_label_L
| <prelift_label_A
| <prelift_label_S
] #H0 destruct
/2 width=3 by ex2_intro/
qed-.

lemma prelift_label_inv_m_sn (f) (l):
      (𝗺) = 🠡[f]l → 𝗺 = l.
#f * [ #k || #F ]
[ <prelift_label_d
| <prelift_label_m
| <prelift_label_z
| <prelift_label_L
| <prelift_label_A
| <prelift_label_S
] #H0 destruct //
qed-.

lemma prelift_label_inv_z_sn (f) (l) (F1):
      (𝘇(f~•F1)) = 🠡[f]l → 𝘇F1 = l.
#f * [ #k || #F ] #F1
[ <prelift_label_d
| <prelift_label_m
| <prelift_label_z
| <prelift_label_L
| <prelift_label_A
| <prelift_label_S
]
#H0 destruct 
<(fbr_coafter_inj_dx … e0) -e0 //
qed-.

lemma prelift_label_inv_L_sn (f) (l):
      (𝗟) = 🠡[f]l → 𝗟 = l.
#f * [ #k || #F ]
[ <prelift_label_d
| <prelift_label_m
| <prelift_label_z
| <prelift_label_L
| <prelift_label_A
| <prelift_label_S
] #H0 destruct //
qed-.

lemma prelift_label_inv_A_sn (f) (l):
      (𝗔) = 🠡[f]l → 𝗔 = l.
#f * [ #k || #F ]
[ <prelift_label_d
| <prelift_label_m
| <prelift_label_z
| <prelift_label_L
| <prelift_label_A
| <prelift_label_S
] #H0 destruct //
qed-.

lemma prelift_label_inv_S_sn (f) (l):
      (𝗦) = 🠡[f]l → 𝗦 = l.
#f * [ #k || #F ]
[ <prelift_label_d
| <prelift_label_m
| <prelift_label_z
| <prelift_label_L
| <prelift_label_A
| <prelift_label_S
] #H0 destruct //
qed-.

(* Main inversions **********************************************************)

theorem prelift_label_inj (f) (l1) (l2):
        🠡[f]l1 = 🠡[f]l2 → l1 = l2.
#f * [ #k1 || #F1 ] #l2 #Hl
[ elim (prelift_label_inv_d_sn … Hl) -Hl #k2 #Hk #H0 destruct
  <(eq_inv_fbr_dapp_bi … Hk) -Hk //
| <(prelift_label_inv_m_sn … Hl) -l2 //
| <(prelift_label_inv_z_sn … Hl) -l2 //
| <(prelift_label_inv_L_sn … Hl) -l2 //
| <(prelift_label_inv_A_sn … Hl) -l2 //
| <(prelift_label_inv_S_sn … Hl) -l2 //
]
qed-.
