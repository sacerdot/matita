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

include "basic_2/syntax/lenv.ma".
include "apps_2/models/model_push.ma".
include "apps_2/notation/models/inwbrackets_4.ma".

(* LOCAL ENVIRONMENT INTERPRETATION  ****************************************)

inductive li (M) (gv): relation2 lenv (evaluation M) ≝
| li_atom: ∀lv. li M gv (⋆) lv
| li_abbr: ∀lv,d,L,V. li M gv L lv → ⟦V⟧[gv, lv] ≗ d → li M gv (L.ⓓV) (⫯[d]lv)
| li_abst: ∀lv,d,L,W. li M gv L lv → li M gv (L.ⓛW) (⫯[d]lv)
| li_unit: ∀lv,d,I,L. li M gv L lv → li M gv (L.ⓤ{I}) (⫯[d]lv)
.

interpretation "local environment interpretation (model)"
   'InWBrackets M gv L lv  = (li M gv L lv).

(* Basic inversion lemmas ***************************************************)

fact li_inv_abbr_aux (M) (gv): ∀v,Y. v ϵ ⟦Y⟧{M}[gv] → ∀L,V. Y = L.ⓓV →
                               ∃∃lv,d. lv ϵ ⟦L⟧{M}[gv] & ⟦V⟧{M}[gv, lv] ≗ d & ⫯{M}[d]lv = v.
#M #gv #v #Y * -v -Y
[ #lv #K #W #H destruct
| #lv #d #L #V #HL #HV #K #W #H destruct /2 width=5 by ex3_2_intro/
| #lv #d #L #V #_ #K #W #H destruct
| #lv #d #I #L #_ #K #W #H destruct
]
qed-.

lemma li_inv_abbr (M) (gv): ∀v,L,V. v ϵ ⟦L.ⓓV⟧{M}[gv] →
                            ∃∃lv,d. lv ϵ ⟦L⟧{M}[gv] & ⟦V⟧{M}[gv, lv] ≗ d & ⫯{M}[d]lv = v.
/2 width=3 by li_inv_abbr_aux/ qed-.

fact li_inv_abst_aux (M) (gv): ∀v,Y. v ϵ ⟦Y⟧{M}[gv] → ∀L,W. Y = L.ⓛW →
                               ∃∃lv,d. lv ϵ ⟦L⟧{M}[gv] & ⫯{M}[d]lv = v.
#M #gv #v #Y * -v -Y
[ #lv #K #U #H destruct
| #lv #d #L #V #_ #_ #K #U #H destruct
| #lv #d #L #V #HL #K #U #H destruct /2 width=4 by ex2_2_intro/
| #lv #d #I #L #_ #K #U #H destruct
]
qed-.

lemma li_inv_abst (M) (gv): ∀v,L,W. v ϵ ⟦L.ⓛW⟧{M}[gv] →
                            ∃∃lv,d. lv ϵ ⟦L⟧{M}[gv] & ⫯{M}[d]lv = v.
/2 width=4 by li_inv_abst_aux/ qed-.

fact li_inv_unit_aux (M) (gv): ∀v,Y. v ϵ ⟦Y⟧{M}[gv] → ∀I,L. Y = L.ⓤ{I} →
                               ∃∃lv,d. lv ϵ ⟦L⟧{M}[gv] & ⫯{M}[d]lv = v.
#M #gv #v #Y * -v -Y
[ #lv #J #K #H destruct
| #lv #d #L #V #_ #_ #J #K #H destruct
| #lv #d #L #V #_ #J #K #H destruct
| #lv #d #I #L #HL #J #K #H destruct /2 width=4 by ex2_2_intro/
]
qed-.

lemma li_inv_unit (M) (gv): ∀v,I,L. v ϵ ⟦L.ⓤ{I}⟧{M}[gv] →
                            ∃∃lv,d. lv ϵ ⟦L⟧{M}[gv] & ⫯{M}[d]lv = v.
/2 width=4 by li_inv_unit_aux/ qed-.
