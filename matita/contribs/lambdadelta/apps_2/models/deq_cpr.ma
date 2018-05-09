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

include "basic_2/rt_transition/cpr.ma".
include "apps_2/models/veq_lifts.ma".
include "apps_2/models/deq.ma".

(* DENOTATIONAL EQUIVALENCE  ************************************************)

(* Forward lemmas with context-sensitive parallel reduction for terms *******)

lemma cpr_fwd_deq (h) (M): is_model M → is_extensional M →
                           ∀G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡[h] T2 → ⦃G, L⦄ ⊢ T1 ≗{M} T2.
#h #M #H1M #H2M #G #L #T1 #T2 #H @(cpr_ind … H) -G -L -T1 -T2
[ /2 width=2 by deq_refl/
| #G #K #V1 #V2 #W2 #_ #IH #HVW2 #gv #v #H
  elim (li_inv_abbr … H) -H #lv #d #HK #Hd #H
  @(mr … H1M) [4,5: @(ti_ext_l … H1M … H) |1,2: skip ] -v
  lapply (lifts_SO_fwd_vlift … gv H1M H2M … HVW2 lv d) -HVW2 #HVW2
  @(seq_trans … H1M … HVW2) -W2
  @(seq_trans … H1M) [3: @IH // | skip ] -G -K -V2
  @(seq_canc_dx … H1M … Hd) -V1 /2 width=1 by ti_lref_vlift_eq/
| #I #G #K #T #U #i #_ #IH #HTU #gv #v #H
  elim (li_fwd_bind … H) -H #lv #d #HK #H
  @(mr … H1M) [4,5: @(ti_ext_l … H1M … H) |1,2: skip ] -v
  lapply (lifts_SO_fwd_vlift … gv H1M H2M … HTU lv d) -HTU #HTU
  @(seq_trans … H1M … HTU) -U
  @(seq_trans … H1M) [3: @IH // | skip ] -G -K -T
  /2 width=1 by ti_lref_vlift_gt/
| #p * #G #L #V1 #V2 #T1 #T2 #_ #_ #IHV #IHT #gv #lv #Hlv
  [ @(mr … H1M) [4,5: @(seq_sym … H1M) @(md … H1M) |1,2: skip ] -p
    @(seq_trans … H1M) [3: @IHT /3 width=1 by li_abbr/ | skip ] -T2
    /4 width=1 by ti_comp_l, veq_refl, vlift_comp/
  | @(mx … H2M) /3 width=1 by li_abst/
  ]
| * #G #L #V1 #V2 #T1 #T2 #_ #_ #IHV #IHT #gv #lv #Hlv
  [ @(mr … H1M) [4,5: @(seq_sym … H1M) @(ma … H1M) |1,2: skip ]
    /3 width=1 by mc/
  | @(mr … H1M) [4,5: @(seq_sym … H1M) @(me … H1M) |1,2: skip ]
    /2 width=1 by/
  ]
| #G #L #V #U1 #U2 #T2 #_ #IH #HTU2 #gv #lv #Hlv
  @(seq_trans … H1M) [2: @(md … H1M) | skip ]
  @(seq_trans … H1M) [2: @IH /3 width=1 by li_abbr, veq_refl/ | skip ] -G -L -U1
  /3 width=1 by lifts_SO_fwd_vlift, seq_sym/
| #G #L #V #T1 #T2 #_ #IH #gv #lv #Hlv
  @(seq_trans … H1M) [2: @(me … H1M) | skip ]
  /2 width=1 by/
| #p #G #L #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #IHV #_ #IHT #gv #lv #Hlv
  @(mr … H1M) [4,5: @(seq_sym … H1M) [ @(ma … H1M) | @(md … H1M) ] |1,2: skip ]
  @(seq_trans … H1M) [3: @IHT /2 width=1 by li_abst/ | skip ] -T2
  @(mr … H1M) [4,5: @(seq_sym … H1M) [ @(mb … H1M) | @(ti_comp_l … H1M) ] |1,2: skip ]
  [2: @vlift_comp [2: @(me … H1M) |4: @(veq_refl … H1M) |1,3: skip ] | skip ]
  /4 width=1 by ti_comp_l, veq_refl, vlift_comp/
| #p #G #L #V1 #V #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #IHV #IHW #IHT #HV2 #gv #lv #Hlv
  @(mr … H1M) [4,5: @(seq_sym … H1M) [ @(ma … H1M) | @(md … H1M) ] |1,2: skip ]
  @(mr … H1M) [4,5: @(seq_sym … H1M) [ @(mc … H1M) | @(ma … H1M) ] |1,2: skip ]
  [2: @IHV // |4: @(md … H1M) |1,3: skip ] -p -V1
  @(mc … H1M) [ /2 width=1 by lifts_SO_fwd_vlift/ ] -V -V2
  @(seq_trans … H1M) [2: @IHT /3 width=1 by li_abbr, veq_refl/ | skip ] -T1
  /4 width=1 by ti_comp_l, veq_refl, vlift_comp/
]
qed-.
