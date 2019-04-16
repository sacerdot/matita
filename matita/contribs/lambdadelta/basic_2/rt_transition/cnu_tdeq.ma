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

include "basic_2/rt_transition/cnr_tdeq.ma".
include "basic_2/rt_transition/cnu_drops.ma".
include "basic_2/rt_transition/cnu_cnr.ma".
include "basic_2/rt_transition/cnu_cnr_simple.ma".

(* NORMAL TERMS FOR T-UNUNBOUND RT-TRANSITION *******************************)

(* Properties with context-free sort-irrelevant equivalence for terms *******)

lemma cnu_dec_tdeq (h) (G) (L):
      ∀T1. ∨∨ ⦃G, L⦄ ⊢ ⥲[h] 𝐍⦃T1⦄
            | ∃∃n,T2. ⦃G, L⦄ ⊢ T1 ➡[n,h] T2 & (T1 ≛ T2 → ⊥).
#h #G #L #T1
@(fqup_wf_ind_eq (Ⓣ) … G L T1) -G -L -T1 #G0 #L0 #T0 #IH #G #L * *
[ #s #HG #HL #HT destruct -IH
  /3 width=5 by cnu_sort, or_introl/
| #i #HG #HL #HT destruct -IH
  elim (drops_F_uni L i)
  [ /3 width=7 by cnu_atom_drops, or_introl/
  | * * [ #I | * #V ] #K #HLK
    [ /3 width=8 by cnu_unit_drops, or_introl/
    | elim (lifts_total V 𝐔❴↑i❵) #W #HVW
      @or_intror @(ex2_2_intro … W) [1,2: /2 width=7 by cpm_delta_drops/ ] #H
      lapply (tdeq_inv_lref1 … H) -H #H destruct
      /2 width=5 by lifts_inv_lref2_uni_lt/
    | elim (lifts_total V 𝐔❴↑i❵) #W #HVW
      @or_intror @(ex2_2_intro … W) [1,2: /2 width=7 by cpm_ell_drops/ ] #H
      lapply (tdeq_inv_lref1 … H) -H #H destruct
      /2 width=5 by lifts_inv_lref2_uni_lt/
    ]
  ]
| #l #HG #HL #HT destruct -IH
  /3 width=5 by cnu_gref, or_introl/
| #p * [ cases p ] #V1 #T1 #HG #HL #HT destruct
  [ elim (cpr_subst h G (L.ⓓV1) T1 0 L V1) [| /2 width=1 by drops_refl/ ] #T2 #X2 #HT12 #HXT2 -IH
    elim (tdeq_dec T1 T2) [ -HT12 #HT12 | #HnT12 ]
    [ elim (tdeq_inv_lifts_dx … HT12 … HXT2) -T2 #X1 #HXT1 #_ -X2
      @or_intror @(ex2_2_intro … X1) [1,2: /2 width=4 by cpm_zeta/ ] #H
      /2 width=7 by tdeq_lifts_inv_pair_sn/
    | @or_intror @(ex2_2_intro … (+ⓓV1.T2)) [1,2: /2 width=2 by cpm_bind/ ] #H
      elim (tdeq_inv_pair … H) -H /2 width=1 by/
    ]
  | elim (cnr_dec_tdeq h G L V1) [ elim (IH G (L.ⓓV1) T1) [| * | // ] | * ] -IH
    [ #HT1 #HV1 /3 width=7 by cnu_abbr_neg, or_introl/
    | #n #T2 #HT12 #HnT12 #_
      @or_intror @(ex2_2_intro … (-ⓓV1.T2)) [1,2: /2 width=2 by cpm_bind/ ] #H
      elim (tdeq_inv_pair … H) -H /2 width=1 by/
    | #V2 #HV12 #HnV12
      @or_intror @(ex2_2_intro … (-ⓓV2.T1)) [1,2: /2 width=2 by cpr_pair_sn/ ] #H
      elim (tdeq_inv_pair … H) -H /2 width=1 by/
    ]
  | elim (cnr_dec_tdeq h G L V1) [ elim (IH G (L.ⓛV1) T1) [| * | // ] | * ] -IH
    [ #HT1 #HV1 /3 width=7 by cnu_abst, or_introl/
    | #n #T2 #HT12 #HnT12 #_
      @or_intror @(ex2_2_intro … (ⓛ{p}V1.T2)) [1,2: /2 width=2 by cpm_bind/ ] #H
      elim (tdeq_inv_pair … H) -H /2 width=1 by/
    | #V2 #HV12 #HnV12
      @or_intror @(ex2_2_intro … (ⓛ{p}V2.T1)) [1,2: /2 width=2 by cpr_pair_sn/ ] #H
      elim (tdeq_inv_pair … H) -H /2 width=1 by/
    ]
  ]
| * #V1 #T1 #HG #HL #HT destruct [| -IH ]
  [ elim (cnr_dec_tdeq h G L V1) [ elim (IH G L T1) [| * | // ] | * ] -IH
    [ #HT1 #HV1
      elim (simple_dec_ex T1) [| * #p * #W1 #U1 #H destruct ]
      [ /3 width=7 by cnu_appl_simple, or_introl/
      | elim (lifts_total V1 𝐔❴1❵) #X1 #HVX1
        @or_intror @(ex2_2_intro … (ⓓ{p}W1.ⓐX1.U1)) [1,2: /2 width=3 by cpm_theta/ ] #H
        elim (tdeq_inv_pair … H) -H #H destruct
      | @or_intror @(ex2_2_intro … (ⓓ{p}ⓝW1.V1.U1)) [1,2: /2 width=2 by cpm_beta/ ] #H
        elim (tdeq_inv_pair … H) -H #H destruct
      ]
    | #n #T2 #HT12 #HnT12 #_
      @or_intror @(ex2_2_intro … (ⓐV1.T2)) [1,2: /2 width=2 by cpm_appl/ ] #H
      elim (tdeq_inv_pair … H) -H /2 width=1 by/
    | #V2 #HV12 #HnV12
      @or_intror @(ex2_2_intro … (ⓐV2.T1)) [1,2: /2 width=2 by cpr_pair_sn/ ] #H
      elim (tdeq_inv_pair … H) -H /2 width=1 by/
    ]
  | @or_intror @(ex2_2_intro … T1) [1,2: /2 width=2 by cpm_eps/ ] #H
    /2 width=4 by tdeq_inv_pair_xy_y/
  ]
]
qed-.
