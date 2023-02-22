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

include "static_2/syntax/fold.ma".
include "apps_2/models/vpushs.ma".

(* MULTIPLE PUSH FOR MODEL EVALUATIONS **************************************)

(* Properties with fold for restricted closures *****************************)

lemma vpushs_fold (M): is_model M → is_extensional M →
                       ∀L,T1,T2,gv,lv.
                       (∀v. L ⨁[gv] lv ≘ v → ⟦T1⟧[gv,v] ≗ ⟦T2⟧[gv,v]) →
                       ⟦L+T1⟧[gv,lv] ≗{M} ⟦L+T2⟧[gv,lv].
#M #H1M #H2M #L elim L -L [| #K * [| * ]]
[ #T1 #T2 #gv #lv #H12
  >fold_atom >fold_atom
  /4 width=1 by vpushs_atom, veq_refl/
| #I #IH #T1 #T2 #gv #lv #H12
  >fold_unit >fold_unit
  /5 width=1 by vpushs_unit, mx, mr/
| #V #IH #T1 #T2 #gv #lv #H12
  >fold_pair >fold_pair
  @IH -IH #v #Hv
  @(mq … H1M) [3:|*: /3 width=2 by seq_sym, md/ ]
  /4 width=1 by vpushs_abbr, mc, mr/
| #W #IH #T1 #T2 #gv #lv #H12
  >fold_pair >fold_pair
  /5 width=1 by vpushs_abst, mx, mr/
]
qed.

(* Inversion lemmas with fold for restricted closures ***********************)

lemma vpushs_inv_fold (M): is_model M → is_injective M →
                           ∀L,T1,T2,gv,lv. ⟦L+T1⟧[gv,lv] ≗{M} ⟦L+T2⟧[gv,lv] →
                           ∀v. L ⨁[gv] lv ≘ v → ⟦T1⟧[gv,v] ≗ ⟦T2⟧[gv,v].
#M #H1M #H2M #L elim L -L [| #K * [| * ]]
[ #T1 #T2 #gv #lv
  >fold_atom >fold_atom #H12 #v #H
  lapply (vpushs_inv_atom … H) -H // #Hv
  /4 width=7 by ti_comp, veq_refl, mq/
| #I #IH #T1 #T2 #gv #lv
  >fold_unit >fold_unit #H12 #y #H
  elim (vpushs_inv_unit … H) -H // #v #d #Hlv #Hv
  lapply (IH … H12 … Hlv) -IH -H12 -Hlv #H12
  /4 width=7 by ti_comp, ti_fwd_mx_dx, veq_refl, mq/
| #V #IH #T1 #T2 #gv #lv
  >fold_pair >fold_pair #H12 #y #H
  elim (vpushs_inv_abbr … H) -H // #v #Hlv #Hv
  lapply (IH … H12 … Hlv) -IH -H12 -Hlv #H12
  @(mq … H1M) [4,5: @(ti_comp … Hv) /3 width=2 by veq_refl/ |1,2: skip ]
  /4 width=7 by ti_comp, ti_fwd_abbr_dx, veq_refl, mq/
| #W #IH #T1 #T2 #gv #lv
  >fold_pair >fold_pair #H12 #y #H
  elim (vpushs_inv_abst … H) -H // #v #d #Hlv #Hv
  lapply (IH … H12 … Hlv) -IH -H12 -Hlv #H12
  /4 width=7 by ti_comp, ti_fwd_mx_dx, veq_refl, mq/
]
qed-.
