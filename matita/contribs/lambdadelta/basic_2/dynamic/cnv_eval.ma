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

include "basic_2/rt_computation/cpmuwe_cpmuwe.ma".
include "basic_2/rt_equivalence/cpes_cpes.ma".
include "basic_2/dynamic/cnv_cpmuwe.ma". (**) (* should be included by the next *)
include "basic_2/dynamic/cnv_cpmuwe_cpmre.ma".
include "basic_2/dynamic/cnv_cpes.ma".
include "basic_2/dynamic/cnv_preserve_cpes.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

(* main properties with evaluations for rt-transition on terms **************)

theorem cnv_dec (h) (a) (G) (L) (T): ac_props a →
        Decidable (❪G,L❫ ⊢ T ![h,a]).
#h #a #G #L #T #Ha
@(fqup_wf_ind_eq (Ⓣ) … G L T) -G -L -T #G0 #L0 #T0 #IH #G #L * * [|||| * ]
[ #s #HG #HL #HT destruct -Ha -IH
  /2 width=1 by cnv_sort, or_introl/
| #i #HG #HL #HT destruct -Ha
  elim (drops_F_uni L i) [| * * ]
  [ /3 width=8 by cnv_inv_lref_atom, or_intror/
  | /3 width=9 by cnv_inv_lref_unit, or_intror/
  | #I #V #K #HLK
    elim (IH G K V) -IH [3: /2 width=2 by fqup_lref/ ]
    [ /3 width=5 by cnv_lref_drops, or_introl/
    | /4 width=5 by cnv_inv_lref_pair, or_intror/
    ]
  ]
| #l #HG #HL #HT destruct -Ha -IH
  /3 width=6 by cnv_inv_gref, or_intror/
| #p #I #V #T #HG #HL #HT destruct -Ha
  elim (IH G L V) [| -IH | // ] #HV
  [ elim (IH G (L.ⓑ[I]V) T) -IH [3: // ] #HT
    [ /3 width=1 by cnv_bind, or_introl/ ]
  ]
  @or_intror #H
  elim (cnv_inv_bind … H) -H /2 width=1 by/
| #V #T #HG #HL #HT destruct
  elim (IH G L V) [| -IH #HV | // ]
  [ elim (IH G L T) -IH [| #HT #HV | // ]
    [ #HT #HV
      elim (cnv_R_cpmuwe_total … HT) #n #Hn
      elim (dec_min (R_cpmuwe h G L T) … Hn) -Hn
      [| /2 width=2 by cnv_R_cpmuwe_dec/ ] #n0 #_ -n
      elim (ac_dec … Ha n0) -Ha
      [ * #n #Ha #Hn * #X0 #HX0 #_
        elim (abst_dec X0)
        [ * #p #W #U0 #H destruct
          elim (cnv_cpes_dec … 1 0 … HV W) [ #HVW | #HnVW ]
          [ lapply (cpmuwe_fwd_cpms … HX0) -HX0 #HTU0
            elim (cnv_fwd_cpms_abst_dx_le … HT … HTU0 … Hn) #U #HTU #_ -U0 -n0
            /3 width=7 by cnv_appl_cpes, or_introl/
(* Note: argument type mismatch *)
          | @or_intror #H -n
            elim (cnv_inv_appl_cpes … H) -H #m0 #q #WX #UX #_ #_ #_ #HVWX #HTUX
            lapply (cpmuwe_abst … HTUX) -HTUX #HTUX
            elim (cnv_cpmuwe_mono … HT … HTUX … HX0) -a -T #H #_
            elim (cpes_fwd_abst_bi … H) -H #_ #HWX -n0 -m0 -p -q -UX -U0
            /3 width=3 by cpes_cpes_trans/
          | lapply (cnv_cpmuwe_trans … HT … HX0) -T #H
            elim (cnv_inv_bind … H) -H #HW #_ //
          ]
(* Note: no expected type *)
        | #HnX0
          @or_intror #H
          elim (cnv_inv_appl_cpes … H) -H #m0 #q #W0 #U0 #_ #_ #_ #_ #HTU0
          lapply (cpmuwe_abst … HTU0) -HTU0 #HTU0
          elim (cnv_cpmuwe_mono … HT … HTU0 … HX0) -T #_ #H
          elim (tweq_inv_abst_sn … H) -W0 -U0 #W0 #U0 #H destruct
          /2 width=4 by/
        ]
(* Note: failed applicability *)
      | #Hge #_ #Hlt
        @or_intror #H
        elim (cnv_inv_appl … H) -H #m0 #q #W0 #U0 #Hm0 #_ #_ #_ #HTU0
        elim (lt_or_ge m0 n0) #H0 [| /3 width=3 by ex2_intro/ ] -Hm0 -Hge
        /4 width=6 by cpmuwe_abst, ex_intro/
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
