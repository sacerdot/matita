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

include "ground_2/relocation/rtmap_basic.ma".
include "static_2/relocation/lifts.ma".
include "apps_2/models/veq.ma".

(* EVALUATION EQUIVALENCE  **************************************************)

(* Forward lemmas with generic relocation ***********************************)

fact lifts_fwd_vpush_aux (M): is_model M → is_extensional M →
                              ∀f,T1,T2. ⬆*[f] T1 ≘ T2 → ∀m. 𝐁❴m,1❵ = f →
                              ∀gv,lv,d. ⟦T1⟧[gv, lv] ≗{M} ⟦T2⟧[gv, ⫯[m←d]lv].
#M #H1M #H2M #f #T1 #T2 #H elim H -f -T1 -T2
[ #f #s #m #Hf #gv #lv #d
  @(mq … H1M) [4,5: /3 width=2 by seq_sym, ms/ |1,2: skip ]
  /2 width=1 by mr/
| #f #i1 #i2 #Hi12 #m #Hm #gv #lv #d destruct
  @(mq … H1M) [4,5: /3 width=2 by seq_sym, ml/ |1,2: skip ]
  elim (lt_or_ge i1 m) #Hi1
  [ lapply (at_basic_inv_lt … Hi12) -Hi12 // #H destruct
    >vpush_lt /2 width=1 by mr/
  | lapply (at_basic_inv_ge … Hi12) -Hi12 // #H destruct
    >vpush_gt /2 width=1 by mr, le_S_S/
  ]
| #f #l #m #Hf #gv #lv #d
  @(mq … H1M) [4,5: /3 width=2 by seq_sym, mg/ |1,2: skip ]
  /2 width=1 by mr/
| #f #p * #V1 #V2 #T1 #T2 #_ #_ #IHV #IHT #m #Hm #gv #lv #d destruct
  [ @(mq … H1M) [4,5: /3 width=2 by seq_sym, md/ |1,2: skip ]
    @(seq_trans … H1M)
    [3: @ti_comp // | skip ]
    [1,2: /2 width=2 by veq_refl/ ]
    [2: @(vpush_comp … H1M) | skip ]
    [1,2: /2 width=2 by/ |3,4: /2 width=2 by veq_refl/ ] -IHV
    @(seq_trans … H1M)
    [3: @ti_comp // | skip ]
    [1,2: /2 width=2 by veq_refl/ ]
    [2: @veq_sym // @vpush_swap // | skip ]
    /2 width=1 by/
  | @mx // [ /2 width=1 by/ ] -IHV #d0
    @(seq_trans … H1M)
    [3: @ti_comp // | skip ]
    [1,2: /2 width=2 by veq_refl/ ]
    [2: @veq_sym // @vpush_swap // | skip ]
    /2 width=1 by/
  ]
| #f * #V1 #v2 #T1 #T2 #_ #_ #IHV #IHT #m #Hm #gv #lv #d
  [ /4 width=5 by seq_sym, ma, mp, mq/
  | /4 width=5 by seq_sym, me, mq/
  ]
]
qed-.

lemma lifts_SO_fwd_vpush (M) (gv): is_model M → is_extensional M →
                                   ∀T1,T2. ⬆*[1] T1 ≘ T2 →
                                   ∀lv,d. ⟦T1⟧[gv, lv] ≗{M} ⟦T2⟧[gv, ⫯[0←d]lv].
/2 width=3 by lifts_fwd_vpush_aux/ qed-.
