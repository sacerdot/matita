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

include "basic_2/rt_computation/cpue_csx.ma".
include "basic_2/rt_equivalence/cpes_cprs.ma".
include "basic_2/dynamic/cnv_cpue.ma".
include "basic_2/dynamic/cnv_cpes.ma".
include "basic_2/dynamic/cnv_preserve_cpes.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

(* main properties with evaluations for rt-transition on terms **************)

theorem cnv_dec (a) (h) (G) (L) (T):
        Decidable (⦃G,L⦄ ⊢ T ![a,h]).
#a #h #G #L #T
@(fqup_wf_ind_eq (Ⓣ) … G L T) -G -L -T #G0 #L0 #T0 #IH #G #L * * [|||| * ]
[ #s #HG #HL #HT destruct -IH
  /2 width=1 by cnv_sort, or_introl/
| #i #HG #HL #HT destruct
  elim (drops_F_uni L i) [| * * ]
  [ /3 width=8 by cnv_inv_lref_atom, or_intror/
  | /3 width=9 by cnv_inv_lref_unit, or_intror/
  | #I #V #K #HLK
    elim (IH G K V) -IH [3: /2 width=2 by fqup_lref/ ]
    [ /3 width=5 by cnv_lref_drops, or_introl/
    | /4 width=5 by cnv_inv_lref_pair, or_intror/
    ]
  ]
| #l #HG #HL #HT destruct -IH
  /3 width=6 by cnv_inv_gref, or_intror/
| #p #I #V #T #HG #HL #HT destruct
  elim (IH G L V) [| -IH | // ] #HV
  [ elim (IH G (L.ⓑ{I}V) T) -IH [3: // ] #HT
    [ /3 width=1 by cnv_bind, or_introl/ ]
  ]
  @or_intror #H
  elim (cnv_inv_bind … H) -H /2 width=1 by/
| #V #T #HG #HL #HT destruct
  elim (IH G L V) [| -IH #HV | // ]
  [ elim (IH G L T) -IH [| #HT #HV | // ]
    [ cases a #HT #HV
      [ elim (cnv_fwd_aaa … HT) #A #HA
        elim (cpme_total_aaa h 1 … HA) #X
        elim (abst_dec X) [ * ]
        [ #p #W #U #H #HTU destruct
          elim (cnv_cpes_dec … 1 0 … HV W) [ #HVW | #HnVW ]
          [ elim HTU -HTU #HTU #_
            /3 width=7 by cnv_appl_cpes, or_introl/
          | @or_intror #H
            elim (cnv_inv_appl_true_cpes … H) -H #q #W0 #U0 #_ #_ #HVW0 #HTU0
            elim (cnv_cpme_cpms_conf … HT … HTU0 … HTU) -T #HU0 #_
            elim (cpms_inv_abst_bi … HU0) -HU0 #_ #HW0 #_ -p -q -U0
            /3 width=3 by cpes_cprs_trans/
          | lapply (cnv_cpme_trans … HT … HTU) -T #H
            elim (cnv_inv_bind … H) -H #HW #_ //
          ]
        | #HnTU #HTX
          @or_intror #H
          elim (cnv_inv_appl_true_cpes … H) -H #q #W0 #U0 #_ #_ #_ #HTU0
          elim (cnv_cpme_cpms_conf … HT … HTU0 … HTX) -T #HX #_
          elim (cpms_inv_abst_sn … HX) -HX #V0 #T0 #_ #_ #H destruct -W0 -U0
          /2 width=4 by/
        ]
      | elim (cpue_total_csx h G L T)
        [| /3 width=2 by cnv_fwd_fsb, fsb_inv_csx/ ] #X
        elim (abst_dec X) [ * ]
        [ #p #W #U #H #HTU destruct
          elim (cnv_cpes_dec … 1 0 … HV W) [ #HVW | #HnVW ]
          [ elim HTU -HTU #n #HTU #_
            @or_introl @(cnv_appl_cpes … HV … HT … HVW … HTU) #H destruct
          | @or_intror #H
            elim (cnv_inv_appl_cpes … H) -H #m1 #q #W0 #U0 #_ #_ #_ #HVW0 #HTU0
            elim (cnv_cpue_cpms_conf … HT … HTU0 … HTU) -m1 -T #X * #m2 #HU0X #_ #HUX
            elim (tueq_inv_bind1 … HUX) -HUX #X0 #_ #H destruct -U
            elim (cpms_inv_abst_bi … HU0X) -HU0X #_ #HW0 #_ -p -q -m2 -U0 -X0
            /3 width=3 by cpes_cprs_trans/
          | lapply (cnv_cpue_trans … HT … HTU) -T #H
            elim (cnv_inv_bind … H) -H #HW #_ //
          ]
        | #HnTU #HTX
          @or_intror #H
          elim (cnv_inv_appl_cpes … H) -H #m1 #q #W0 #U0 #_ #_ #_ #_ #HTU0
          elim (cnv_cpue_cpms_conf … HT … HTU0 … HTX) -m1 -T #X0 * #m2 #HUX0 #_ #HX0
          elim (cpms_inv_abst_sn … HUX0) -HUX0 #V0 #T0 #_ #_ #H destruct -m2 -W0 -U0
          elim (tueq_inv_bind2 … HX0) -HX0 #X0 #_ #H destruct
          /2 width=4 by/
        ]
      ]
    ]
  ]
  @or_intror #H
  elim (cnv_inv_appl … H) -H /2 width=1 by/
| #U #T #HG #HL #HT destruct
  elim (IH G L U) [| -IH | // ] #HU
  [ elim (IH G L T) -IH [3: // ] #HT
    [ elim (cnv_cpes_dec … 0 1 … HU … HT) #HUT
      [ /3 width=1 by cnv_cast_cpes, or_introl/ ]
    ]
  ]
  @or_intror #H
  elim (cnv_inv_cast_cpes … H) -H /2 width=1 by/
]
qed-.
