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

include "basic_2/rt_computation/cnuw_simple.ma".
include "basic_2/rt_computation/cnuw_drops.ma".
include "basic_2/rt_computation/cprs_tweq.ma".
include "basic_2/rt_computation/lprs_cpms.ma".

(* NORMAL TERMS FOR T-UNUNBOUND WHD RT-TRANSITION ***************************)

(* Advanced inversion lemmas ************************************************)

lemma cnuw_inv_abbr_pos (h) (G) (L):
      ∀V,T. ❪G,L❫ ⊢ ➡𝐍𝐖*[h] +ⓓV.T → ⊥.
#h #G #L #V #T1 #H
elim (cprs_abbr_pos_twneq h G L V T1) #T2 #HT12 #HnT12
/3 width=2 by/
qed-.

(* Advanced properties ******************************************************)

lemma cnuw_abbr_neg (h) (G) (L): ∀V,T. ❪G,L❫ ⊢ ➡𝐍𝐖*[h] -ⓓV.T.
#h #G #L #V1 #T1 #n #X #H
elim (cpms_inv_abbr_sn_dx … H) -H *
[ #V2 #T2 #_ #_ #H destruct /1 width=1 by tweq_abbr_neg/
| #X1 #_ #_ #H destruct
]
qed.

lemma cnuw_abst (h) (p) (G) (L): ∀W,T. ❪G,L❫ ⊢ ➡𝐍𝐖*[h] ⓛ[p]W.T.
#h #p #G #L #W1 #T1 #n #X #H
elim (cpms_inv_abst_sn … H) -H #W2 #T2 #_ #_ #H destruct
/1 width=1 by tweq_abst/
qed.

lemma cnuw_cpms_trans (h) (n) (G) (L):
      ∀T1. ❪G,L❫ ⊢ ➡𝐍𝐖*[h] T1 →
      ∀T2. ❪G,L❫ ⊢ T1 ➡*[n,h] T2 → ❪G,L❫ ⊢ ➡𝐍𝐖*[h] T2.
#h #n1 #G #L #T1 #HT1 #T2 #HT12 #n2 #T3 #HT23
/4 width=5 by cpms_trans, tweq_canc_sn/
qed-.

lemma cnuw_dec_ex (h) (G) (L):
      ∀T1. ∨∨ ❪G,L❫ ⊢ ➡𝐍𝐖*[h] T1
            | ∃∃n,T2. ❪G,L❫ ⊢ T1 ➡*[n,h] T2 & (T1 ≅ T2 → ⊥).
#h #G #L #T1 elim T1 -T1 *
[ #s /3 width=5 by cnuw_sort, or_introl/
| #i elim (drops_F_uni L i)
  [ /3 width=7 by cnuw_atom_drops, or_introl/
  | * * [ #I | * #V ] #K #HLK
    [ /3 width=8 by cnuw_unit_drops, or_introl/
    | elim (lifts_total V 𝐔❨↑i❩) #W #HVW
      @or_intror @(ex2_2_intro … W) [1,2: /2 width=7 by cpms_delta_drops/ ] #H
      lapply (tweq_inv_lref_sn … H) -H #H destruct
      /2 width=5 by lifts_inv_lref2_uni_lt/
    | elim (lifts_total V 𝐔❨↑i❩) #W #HVW
      @or_intror @(ex2_2_intro … W) [1,2: /2 width=7 by cpms_ell_drops/ ] #H
      lapply (tweq_inv_lref_sn … H) -H #H destruct
      /2 width=5 by lifts_inv_lref2_uni_lt/
    ]
  ]
| #l /3 width=5 by cnuw_gref, or_introl/
| #p * [ cases p ] #V1 #T1 #_ #_
  [ elim (cprs_abbr_pos_twneq h G L V1 T1) #T2 #HT12 #HnT12
    /4 width=4 by ex2_2_intro, or_intror/
  | /3 width=5 by cnuw_abbr_neg, or_introl/
  | /3 width=5 by cnuw_abst, or_introl/
  ]
| * #V1 #T1 #_ #IH
  [ elim (simple_dec_ex T1) [ #HT1 | * #p * #W1 #U1 #H destruct ]
    [ elim IH -IH
      [ /3 width=6 by cnuw_appl_simple, or_introl/
      | * #n #T2 #HT12 #HnT12 -HT1
        @or_intror @(ex2_2_intro … n (ⓐV1.T2)) [ /2 width=1 by cpms_appl_dx/ ] #H
        lapply (tweq_inv_appl_bi … H) -H /2 width=1 by/
      ]
    | elim (lifts_total V1 𝐔❨1❩) #X1 #HVX1
      @or_intror @(ex2_2_intro … (ⓓ[p]W1.ⓐX1.U1)) [1,2: /2 width=3 by cpms_theta/ ] #H
      elim (tweq_inv_appl_sn … H) -H #X1 #X2 #_ #H destruct
    | @or_intror @(ex2_2_intro … (ⓓ[p]ⓝW1.V1.U1)) [1,2: /2 width=2 by cpms_beta/ ] #H
      elim (tweq_inv_appl_sn … H) -H #X1 #X2 #_ #H destruct
    ]
  | @or_intror @(ex2_2_intro … T1) [1,2: /2 width=2 by cpms_eps/ ] #H
    /2 width=4 by tweq_inv_cast_xy_y/
  ]
]
qed-.

lemma cnuw_dec (h) (G) (L): ∀T. Decidable (❪G,L❫ ⊢ ➡𝐍𝐖*[h] T).
#h #G #L #T1
elim (cnuw_dec_ex h G L T1)
[ /2 width=1 by or_introl/
| * #n #T2 #HT12 #nT12 /4 width=2 by or_intror/
]
qed-.
