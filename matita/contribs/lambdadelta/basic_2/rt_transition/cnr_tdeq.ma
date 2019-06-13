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

include "static_2/relocation/lifts_tdeq.ma".
include "basic_2/rt_transition/cpr_drops_basic.ma".
include "basic_2/rt_transition/cnr_simple.ma".
include "basic_2/rt_transition/cnr_drops.ma".

(* NORMAL TERMS FOR CONTEXT-SENSITIVE R-TRANSITION **************************)

(* Properties with context-free sort-irrelevant equivalence for terms *******)

(* Basic_1: was: nf2_dec *)
(* Basic_2A1: uses: cnr_dec *)
lemma cnr_dec_tdeq (h) (G) (L):
      ∀T1. ∨∨ ⦃G,L⦄ ⊢ ➡[h] 𝐍⦃T1⦄
            | ∃∃T2. ⦃G,L⦄ ⊢ T1 ➡[h] T2 & (T1 ≛ T2 → ⊥).
#h #G #L #T1
@(fqup_wf_ind_eq (Ⓣ) … G L T1) -G -L -T1 #G0 #L0 #T0 #IH #G #L * *
[ #s #HG #HL #HT destruct -IH
  /3 width=4 by cnr_sort, or_introl/
| #i #HG #HL #HT destruct -IH
  elim (drops_F_uni L i)
  [ /3 width=6 by cnr_lref_atom, or_introl/
  | * * [ #I | * #V ] #K #HLK
    [ /3 width=7 by cnr_lref_unit, or_introl/
    | elim (lifts_total V 𝐔❴↑i❵) #W #HVW
      @or_intror @(ex2_intro … W) [ /2 width=6 by cpm_delta_drops/ ] #H
      lapply (tdeq_inv_lref1 … H) -H #H destruct
      /2 width=5 by lifts_inv_lref2_uni_lt/
    | /3 width=7 by cnr_lref_abst, or_introl/
    ]
  ]
| #l #HG #HL #HT destruct -IH
  /3 width=4 by cnr_gref, or_introl/
| #p * [ cases p ] #V1 #T1 #HG #HL #HT destruct
  [ elim (cpr_subst h G (L.ⓓV1) T1 0 L V1) [| /2 width=1 by drops_refl/ ] #T2 #X2 #HT12 #HXT2 -IH
    elim (tdeq_dec T1 T2) [ -HT12 #HT12 | #HnT12 ]
    [ elim (tdeq_inv_lifts_dx … HT12 … HXT2) -T2 #X1 #HXT1 #_ -X2
      @or_intror @(ex2_intro … X1) [ /2 width=3 by cpm_zeta/ ] #H
      /2 width=7 by tdeq_lifts_inv_pair_sn/
    | @or_intror @(ex2_intro … (+ⓓV1.T2)) [ /2 width=1 by cpm_bind/ ] #H
      elim (tdeq_inv_pair … H) -H /2 width=1 by/
    ]
  | elim (IH G L V1) [ elim (IH G (L.ⓓV1) T1) [| * | // ] | * | // ] -IH
    [ #HT1 #HV1 /3 width=6 by cnr_abbr_neg, or_introl/
    | #T2 #HT12 #HnT12 #_
      @or_intror @(ex2_intro … (-ⓓV1.T2)) [ /2 width=1 by cpm_bind/ ] #H
      elim (tdeq_inv_pair … H) -H /2 width=1 by/
    | #V2 #HV12 #HnV12
      @or_intror @(ex2_intro … (-ⓓV2.T1)) [ /2 width=1 by cpr_pair_sn/ ] #H
      elim (tdeq_inv_pair … H) -H /2 width=1 by/
    ]
  | elim (IH G L V1) [ elim (IH G (L.ⓛV1) T1) [| * | // ] | * | // ] -IH
    [ #HT1 #HV1 /3 width=6 by cnr_abst, or_introl/
    | #T2 #HT12 #HnT12 #_
      @or_intror @(ex2_intro … (ⓛ{p}V1.T2)) [ /2 width=1 by cpm_bind/ ] #H
      elim (tdeq_inv_pair … H) -H /2 width=1 by/
    | #V2 #HV12 #HnV12
      @or_intror @(ex2_intro … (ⓛ{p}V2.T1)) [ /2 width=1 by cpr_pair_sn/ ] #H
      elim (tdeq_inv_pair … H) -H /2 width=1 by/
    ]
  ]
| * #V1 #T1 #HG #HL #HT destruct [| -IH ]
  [ elim (IH G L V1) [ elim (IH G L T1) [| * | // ] | * | // ] -IH
    [ #HT1 #HV1
      elim (simple_dec_ex T1) [| * #p * #W1 #U1 #H destruct ]
      [ /3 width=6 by cnr_appl_simple, or_introl/
      | elim (lifts_total V1 𝐔❴1❵) #X1 #HVX1
        @or_intror @(ex2_intro … (ⓓ{p}W1.ⓐX1.U1)) [ /2 width=3 by cpm_theta/ ] #H
        elim (tdeq_inv_pair … H) -H #H destruct
      | @or_intror @(ex2_intro … (ⓓ{p}ⓝW1.V1.U1)) [ /2 width=1 by cpm_beta/ ] #H
        elim (tdeq_inv_pair … H) -H #H destruct
      ]
    | #T2 #HT12 #HnT12 #_
      @or_intror @(ex2_intro … (ⓐV1.T2)) [ /2 width=1 by cpm_appl/ ] #H
      elim (tdeq_inv_pair … H) -H /2 width=1 by/
    | #V2 #HV12 #HnV12
      @or_intror @(ex2_intro … (ⓐV2.T1)) [ /2 width=1 by cpr_pair_sn/ ] #H
      elim (tdeq_inv_pair … H) -H /2 width=1 by/
    ]
  | @or_intror @(ex2_intro … T1) [ /2 width=1 by cpm_eps/ ] #H
    /2 width=4 by tdeq_inv_pair_xy_y/
  ]
]
qed-.
