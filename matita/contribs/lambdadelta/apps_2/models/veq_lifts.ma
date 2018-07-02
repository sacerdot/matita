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

fact lifts_fwd_vlift_aux (M) (gv): is_model M → is_extensional M →
                                   ∀f,T1,T2. ⬆*[f] T1 ≘ T2 → ∀m. 𝐁❴m,1❵ = f →
                                   ∀lv,d. ⟦T1⟧[gv, lv] ≗{M} ⟦T2⟧[gv, ⫯[m←d]lv].
#M #gv #H1M #H2M #f #T1 #T2 #H elim H -f -T1 -T2
[ /4 width=3 by seq_trans, seq_sym, ms/
| #f #i1 #i2 #Hi12 #m #Hm #lv #d destruct
  @(mr … H1M) [4,5: @(seq_sym … H1M) @(ml … H1M) |1,2: skip ]
  elim (lt_or_ge i1 m) #Hi1
  [ lapply (at_basic_inv_lt … Hi12) -Hi12 // #H destruct
    >vlift_lt /2 width=1 by mq/
  | lapply (at_basic_inv_ge … Hi12) -Hi12 // #H destruct
    >vlift_gt /2 width=1 by mq, le_S_S/
  ]
| /4 width=3 by seq_trans, seq_sym, mg/
| #f #p * #V1 #V2 #T1 #T2 #_ #_ #IHV #IHT #m #Hm #lv #d destruct
  [ @(mr … H1M) [4,5: @(seq_sym … H1M) @(md … H1M) |1,2: skip ]
    @(seq_trans … H1M)
    [2: @(ti_comp_l … H1M) | skip ]
    [2: @(vlift_comp … lv lv) | skip ]
    [3: /2 width=1 by veq_refl/ ]
    [2: @(IHV … d) // | skip ]
    @(seq_trans … H1M) [2: @(IHT (↑m) … d) // | skip ]
    /4 width=1 by seq_sym, ti_ext_l, vlift_swap/
  | @mx /2 width=1 by/ #d0 @(seq_trans … H1M)
    [3: @(seq_sym … H1M) @(ti_ext_l … H1M) | skip ]
    [2: @vlift_swap // | skip ]
    /2 width=1 by/
  ]
| #f * #V1 #v2 #T1 #T2 #_ #_ #IHV #IHT #m #Hm #lv #d
  [ /4 width=5 by seq_sym, ma, mc, mr/
  | /4 width=5 by seq_sym, me, mr/
  ]
]
qed-.

lemma lifts_SO_fwd_vlift (M) (gv): is_model M → is_extensional M →
                                   ∀T1,T2. ⬆*[1] T1 ≘ T2 →
                                   ∀lv,d. ⟦T1⟧[gv, lv] ≗{M} ⟦T2⟧[gv, ⫯[d]lv].
/2 width=3 by lifts_fwd_vlift_aux/ qed-.
