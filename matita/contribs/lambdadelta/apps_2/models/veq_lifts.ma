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

include "basic_2/relocation/lifts.ma".
include "apps_2/models/veq.ma".

(* EVALUATION EQUIVALENCE  **************************************************)

lemma pippo (M) (gv): is_model M → is_extensional M →
                      ∀f,T1,T2. ⬆*[f] T1 ≘ T2 → ∀n. ⫯*[n] 𝐔❴1❵ = f →
                      ∀lv,d. ⟦T1⟧[gv, lv] ≗{M} ⟦T2⟧[gv, ⫯[n←d]lv]. 
#M #gv #H1M #H2M #f #T1 #T2 #H elim H -f -T1 -T2
[ /4 width=3 by seq_trans, seq_sym, ms/
| #f #i1 #i2 #Hi12 #n #Hn #lv #d
  @(mr … H1M) [4,5: @(seq_sym … H1M) @(ml … H1M) |1,2: skip ]
| /4 width=3 by seq_trans, seq_sym, mg/
| #f #p * #V1 #V2 #T1 #T2 #_ #_ #IHV #IHT #n #Hn #lv #d
  [ @(mr … H1M) [4,5: @(seq_sym … H1M) @(md … H1M) |1,2: skip ]
    @(seq_trans … H1M)
    [2: @(ti_comp_l … H1M) | skip ]
    [2: @(vlift_comp … lv lv) | skip ]
    [3: /2 width=1 by veq_refl/ ]
    [2: @(IHV … d) // | skip ]
    @(seq_trans … H1M) [2: @(IHT … d) // | skip ]
    /4 width=1 by seq_sym, ti_ext_l, vlift_swap/
  | @mx /2 width=1 by/ #d0 @(seq_trans … H1M)
    [3: @(seq_sym … H1M) @(ti_ext_l … H1M) | skip ]
    [2: @vlift_swap // | skip ]
    /2 width=1 by/
  ]
| #f * #V1 #v2 #T1 #T2 #_ #_ #IHV #IHT #n #Hn #lv #d
  [ /4 width=5 by seq_sym, ma, mc, mr/
  | /4 width=5 by seq_sym, me, mr/
  ]
]  
