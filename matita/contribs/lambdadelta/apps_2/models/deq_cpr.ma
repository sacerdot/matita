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
  elim (li_inv_abbr … H) -H // #lv #HK #H
  @(mq … H1M) [4,5: @(ti_comp … H) /2 width=2 by veq_refl/ |1,2: skip ] -v
  @(mq … H1M)
  [4: /3 width=1 by seq_sym, ml/ | skip
  |5: /2 width=2 by lifts_SO_fwd_vlift/ | skip ] -W2
  >vlift_eq /2 width=1 by/
| #I #G #K #T #U #i #_ #IH #HTU #gv #v #H
  elim (li_fwd_bind … H) // -H #lv #d #HK #H
  @(mq … H1M) [4,5: @(ti_comp … H) /2 width=2 by veq_refl/ |1,2: skip ] -v
  @(mq … H1M)
  [4: /3 width=1 by seq_sym, ml/ | skip
  |5: /2 width=2 by lifts_SO_fwd_vlift/ | skip ] -U
  >vlift_gt /3 width=5 by ml, mq, mr/
| #p * #G #L #V1 #V2 #T1 #T2 #_ #_ #IHV #IHT #gv #lv #Hlv
  [ @(mq … H1M) [4,5: /3 width=2 by seq_sym, md/ |1,2: skip ] -p
    @(seq_trans … H1M) [2: @IHT /2 width=1 by li_abbr/ | skip ] -T1
    /4 width=1 by ti_comp, vlift_comp, (* 2x *) veq_refl/
  | /4 width=1 by li_abst, mx/
  ]
| * #G #L #V1 #V2 #T1 #T2 #_ #_ #IHV #IHT #gv #lv #Hlv
  [ @(mq … H1M) [4,5: /3 width=2 by seq_sym, ma/ |1,2: skip ]
    /3 width=1 by mp/
  | @(mq … H1M) [4,5: /3 width=2 by seq_sym, me/ |1,2: skip ]
    /2 width=1 by/
  ]
| #G #L #V #U1 #U2 #T2 #_ #IH #HTU2 #gv #lv #Hlv
  @(mq … H1M)
  [4: /3 width=2 by seq_sym, md/ | skip
  |3: /3 width=1 by li_abbr/ | skip ] -L -U1
  /3 width=1 by lifts_SO_fwd_vlift, seq_sym/
| #G #L #V #T1 #T2 #_ #IH #gv #lv #Hlv
  @(seq_trans … H1M) [2: @(me … H1M) | skip ]
  /2 width=1 by/
| #p #G #L #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #IHV #_ #IHT #gv #lv #Hlv
  @(mq … H1M) [4,5: /3 width=2 by seq_sym, ma, md/ |1,2: skip ]
  @(mq … H1M)
  [4: /3 width=2 by seq_sym, mb/ | skip
  |5: @IHT /2 width=1 by li_abst/ | skip ] -T2
  @ti_comp /2 width=1 by veq_refl/
  @vlift_comp /2 width=1 by veq_refl/
  @(mq … H1M) [4,5: /3 width=2 by seq_sym, me/ |1,2: skip ] -L -V1
  /2 width=1 by mr/
| #p #G #L #V1 #V #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #IHV #IHW #IHT #HV2 #gv #lv #Hlv
  @(mq … H1M) [4,5: /3 width=2 by seq_sym, ma, md/ |1,2: skip ]
  @(seq_trans … H1M) [3: /3 width=1 by seq_sym, ma/ | skip ]
  @mp // [ @(seq_trans … H1M) /3 width=3 by lifts_SO_fwd_vlift/ ] -V1 -V -V2
  @(mq … H1M)
  [4: /3 width=2 by seq_sym, md/ | skip
  |3: @IHT /2 width=1 by li_abbr/ | skip ] -T1
  /4 width=1 by ti_comp, vlift_comp, (* 2x *) veq_refl/
]
qed-.
