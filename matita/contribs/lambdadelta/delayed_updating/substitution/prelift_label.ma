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
include "ground/relocation/tr_pap_pap.ma".

(* PRELIFT FOR LABEL ********************************************************)

definition prelift_label (f) (l): label â
match l with
[ label_d k â ğ±(fï¼ â§£â¨kâ©)
| label_m   â ğº
| label_L   â ğ
| label_A   â ğ
| label_S   â ğ¦
].

interpretation
  "prelift (label)"
  'UpTriangleArrow f l = (prelift_label f l).

(* Basic constructions ******************************************************)

lemma prelift_label_d (f) (k):
      (ğ±(fï¼ â§£â¨kâ©)) = ğ ¡[f]ğ±k.
// qed.

lemma prelift_label_m (f):
      (ğº) = ğ ¡[f]ğº.
// qed.

lemma prelift_label_L (f):
      (ğ) = ğ ¡[f]ğ.
// qed.

lemma prelift_label_A (f):
      (ğ) = ğ ¡[f]ğ.
// qed.

lemma prelift_label_S (f):
      (ğ¦) = ğ ¡[f]ğ¦.
// qed.

(* Basic inversions *********************************************************)

lemma prelift_label_inv_d_sn (f) (l) (k1):
      (ğ±k1) = ğ ¡[f]l â
      ââk2. k1 = fï¼ â§£â¨k2â© & ğ±k2 = l.
#f * [ #k ] #k1
[ <prelift_label_d
| <prelift_label_m
| <prelift_label_L
| <prelift_label_A
| <prelift_label_S
] #H0 destruct
/2 width=3 by ex2_intro/
qed-.

lemma prelift_label_inv_m_sn (f) (l):
      (ğº) = ğ ¡[f]l â ğº = l.
#f * [ #k ]
[ <prelift_label_d
| <prelift_label_m
| <prelift_label_L
| <prelift_label_A
| <prelift_label_S
] #H0 destruct //
qed-.

lemma prelift_label_inv_L_sn (f) (l):
      (ğ) = ğ ¡[f]l â ğ = l.
#f * [ #k ]
[ <prelift_label_d
| <prelift_label_m
| <prelift_label_L
| <prelift_label_A
| <prelift_label_S
] #H0 destruct //
qed-.

lemma prelift_label_inv_A_sn (f) (l):
      (ğ) = ğ ¡[f]l â ğ = l.
#f * [ #k ]
[ <prelift_label_d
| <prelift_label_m
| <prelift_label_L
| <prelift_label_A
| <prelift_label_S
] #H0 destruct //
qed-.

lemma prelift_label_inv_S_sn (f) (l):
      (ğ¦) = ğ ¡[f]l â ğ¦ = l.
#f * [ #k ]
[ <prelift_label_d
| <prelift_label_m
| <prelift_label_L
| <prelift_label_A
| <prelift_label_S
] #H0 destruct //
qed-.

(* Main inversions **********************************************************)

theorem prelift_label_inj (f) (l1) (l2):
        ğ ¡[f]l1 = ğ ¡[f]l2 â l1 = l2.
#f * [ #k1 ] #l2 #Hl
[ elim (prelift_label_inv_d_sn â¦ Hl) -Hl #k2 #Hk #H0 destruct
  >(tr_pap_inj ???? Hk) -Hk //
| <(prelift_label_inv_m_sn â¦ Hl) -l2 //
| <(prelift_label_inv_L_sn â¦ Hl) -l2 //
| <(prelift_label_inv_A_sn â¦ Hl) -l2 //
| <(prelift_label_inv_S_sn â¦ Hl) -l2 //
]
qed-.
