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

include "static_2/syntax/shift.ma".
include "apps_2/models/vlifts.ma".

(* MULTIPLE LIFT FOR MODEL EVALUATIONS **************************************)

(* Properties with shift for restricted closures ****************************)

lemma vlifts_shift (M): is_model M → is_extensional M →
                        ∀L,T1,T2,gv,lv.
                        (∀v. L ⨁[gv] lv ≘ v → ⟦T1⟧[gv, v] ≗ ⟦T2⟧[gv, v]) → 
                        ⟦L+T1⟧[gv, lv] ≗{M} ⟦L+T2⟧[gv, lv].
#M #H1M #H2M #L elim L -L [| #K * [| * ]]
[ #T1 #T2 #gv #lv #H12
  >shift_atom >shift_atom
  /4 width=1 by vlifts_atom, veq_refl/
| #I #IH #T1 #T2 #gv #lv #H12
  >shift_unit >shift_unit
  /5 width=1 by vlifts_unit, mx, mr/
| #V #IH #T1 #T2 #gv #lv #H12
  >shift_pair >shift_pair
  @IH -IH #v #Hv
  @(mq … H1M) [3:|*: /3 width=2 by seq_sym, md/ ]
  /4 width=1 by vlifts_abbr, mr/
| #W #IH #T1 #T2 #gv #lv #H12
  >shift_pair >shift_pair
  /5 width=1 by vlifts_abst, mx, mr/
]
qed.

(* Inversion lemmas with shift for restricted closures **********************)

lemma vlifts_inv_shift (M): is_model M →
                            ∀L,T1,T2,gv,lv. ⟦L+T1⟧[gv, lv] ≗{M} ⟦L+T2⟧[gv, lv] →
                            ∀v. L ⨁[gv] lv ≘ v → ⟦T1⟧[gv, v] ≗ ⟦T2⟧[gv, v].
#M #HM #L elim L -L [| #K * [| * ]]
[ #T1 #T2 #gv #lv
  >shift_atom >shift_atom #H12 #v #H
  lapply (vlifts_inv_atom … H) -H // #Hv
  /4 width=7 by ti_comp, veq_refl, mq/
| #I #IH #T1 #T2 #gv #lv
  >shift_unit >shift_unit #H12 #y #H
  elim (vlifts_inv_unit … H) -H // #v #d #Hlv #Hv
  lapply (IH … H12 … Hlv) -IH -H12 -Hlv #H12
  /4 width=7 by ti_comp, ti_fwd_mx_dx, veq_refl, mq/
| #V #IH #T1 #T2 #gv #lv
  >shift_pair >shift_pair #H12 #y #H
  elim (vlifts_inv_abbr … H) -H // #v #Hlv #Hv
  lapply (IH … H12 … Hlv) -IH -H12 -Hlv #H12
  /4 width=7 by ti_comp, veq_refl, md, mq/
| #W #IH #T1 #T2 #gv #lv
  >shift_pair >shift_pair #H12 #y #H
  elim (vlifts_inv_abst … H) -H // #v #d #Hlv #Hv
  lapply (IH … H12 … Hlv) -IH -H12 -Hlv #H12
  /4 width=7 by ti_comp, ti_fwd_mx_dx, veq_refl, mq/
]
qed-.
