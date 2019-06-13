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

include "static_2/syntax/lenv.ma".
include "apps_2/models/veq.ma".
include "apps_2/notation/models/inwbrackets_4.ma".

(* LOCAL ENVIRONMENT INTERPRETATION  ****************************************)

inductive li (M) (gv): relation2 lenv (evaluation M) ≝
| li_atom: ∀lv. li M gv (⋆) lv
| li_abbr: ∀lv,d,L,V. li M gv L lv → ⟦V⟧[gv,lv] = d → li M gv (L.ⓓV) (⫯[0←d]lv)
| li_abst: ∀lv,d,L,W. li M gv L lv → li M gv (L.ⓛW) (⫯[0←d]lv)
| li_unit: ∀lv,d,I,L. li M gv L lv → li M gv (L.ⓤ{I}) (⫯[0←d]lv)
| li_veq : ∀lv1,lv2,L. li M gv L lv1 → lv1 ≗ lv2 → li M gv L lv2
.

interpretation "local environment interpretation (model)"
   'InWBrackets M gv L lv  = (li M gv L lv).

(* Basic inversion lemmas ***************************************************)

fact li_inv_abbr_aux (M) (gv): is_model M → 
                               ∀v,Y. v ϵ ⟦Y⟧{M}[gv] → ∀L,V. Y = L.ⓓV →
                               ∃∃lv. lv ϵ ⟦L⟧[gv] & ⫯[0←⟦V⟧[gv,lv]]lv ≗ v.
#M #gv #HM #v #Y #H elim H -v -Y
[ #lv #K #W #H destruct
| #lv #d #L #V #HL #HV #_ #K #W #H destruct
  /3 width=3 by veq_refl, ex2_intro/
| #lv #d #L #V #_ #_ #K #W #H destruct
| #lv #d #I #L #_ #_ #K #W #H destruct
| #lv1 #lv2 #L #_ #Hlv12 #IH #K #W #H destruct
  elim IH -IH [|*: // ] #lv #HK #HW
  /3 width=5 by veq_trans, ex2_intro/
]
qed-.

lemma li_inv_abbr (M) (gv): is_model M →
                            ∀v,L,V. v ϵ ⟦L.ⓓV⟧{M}[gv] →
                            ∃∃lv. lv ϵ ⟦L⟧[gv] & ⫯[0←⟦V⟧[gv,lv]]lv ≗ v.
/2 width=3 by li_inv_abbr_aux/ qed-.

fact li_inv_abst_aux (M) (gv): is_model M →
                               ∀v,Y. v ϵ ⟦Y⟧{M}[gv] → ∀L,W. Y = L.ⓛW →
                               ∃∃lv,d. lv ϵ ⟦L⟧[gv] & ⫯[0←d]lv ≗ v.
#M #gv #HM #v #Y #H elim H -v -Y
[ #lv #K #U #H destruct
| #lv #d #L #V #_ #_ #_ #K #U #H destruct
| #lv #d #L #V #HL #_ #K #U #H destruct
  /3 width=4 by veq_refl, ex2_2_intro/
| #lv #d #I #L #_ #_ #K #U #H destruct
| #lv1 #lv2 #L #_ #Hlv12 #IH #K #U #H destruct
  elim IH -IH [|*: // ] #lv #d #HK #Hlv
  /3 width=6 by veq_trans, ex2_2_intro/
]
qed-.

lemma li_inv_abst (M) (gv): is_model M →
                            ∀v,L,W. v ϵ ⟦L.ⓛW⟧{M}[gv] →
                            ∃∃lv,d. lv ϵ ⟦L⟧[gv] & ⫯[0←d]lv ≗ v.
/2 width=4 by li_inv_abst_aux/ qed-.

fact li_inv_unit_aux (M) (gv): is_model M →
                               ∀v,Y. v ϵ ⟦Y⟧{M}[gv] → ∀I,L. Y = L.ⓤ{I} →
                               ∃∃lv,d. lv ϵ ⟦L⟧[gv] & ⫯[0←d]lv ≗ v.
#M #gv #HM #v #Y #H elim H -v -Y
[ #lv #J #K #H destruct
| #lv #d #L #V #_ #_ #_ #J #K #H destruct
| #lv #d #L #V #_ #_ #J #K #H destruct
| #lv #d #I #L #HL #_ #J #K #H destruct
  /3 width=4 by veq_refl, ex2_2_intro/
| #lv1 #lv2 #L #_ #Hlv12 #IH #J #K #H destruct
  elim IH -IH [|*: // ] #lv #d #HK #Hlv
  /3 width=6 by veq_trans, ex2_2_intro/
]
qed-.

lemma li_inv_unit (M) (gv): is_model M →
                            ∀v,I,L. v ϵ ⟦L.ⓤ{I}⟧{M}[gv] →
                            ∃∃lv,d. lv ϵ ⟦L⟧[gv] & ⫯[0←d]lv ≗ v.
/2 width=4 by li_inv_unit_aux/ qed-.

(* Advanced forward lemmas **************************************************)

lemma li_fwd_bind (M) (gv): is_model M →
                            ∀v,I,L. v ϵ ⟦L.ⓘ{I}⟧{M}[gv] →
                            ∃∃lv,d. lv ϵ ⟦L⟧[gv] & ⫯[0←d]lv ≗ v.
#M #gv #HM #v * [ #I | * #V ] #L #H
[ /2 width=2 by li_inv_unit/
| elim (li_inv_abbr … H) // -H #lv #HL #Hv
  /2 width=4 by ex2_2_intro/
| /2 width=2 by li_inv_abst/
]
qed-.

(* Basic_properties *********************************************************)

lemma li_repl (M) (L): is_model M ->
                       replace_2 … (λgv.li M gv L) (veq …) (veq …).
#M #L #HM #gv1 #lv1 #H elim H -L -lv1
[ #lv1 #gv2 #Hgv #lv2 #Hlv /2 width=1 by li_atom/
| #lv1 #d #K #V #_ #Hd #IH #gv2 #Hgv #lv2 #Hlv destruct
  @li_veq [2: /4 width=4 by li_abbr, veq_refl/ | skip ] -IH
  @(veq_canc_sn … Hlv) -Hlv //
  /4 width=1 by ti_comp, vpush_comp, (* 2x *) veq_refl/
| #lv1 #d #K #W #_ #IH #gv2 #Hgv #lv2 #Hlv
  @li_veq /4 width=3 by li_abst, veq_refl/
| #lv1 #d #I #K #_ #IH #gv2 #Hgv #lv2 #Hlv
  @li_veq /4 width=3 by li_unit, veq_refl/
| #lv1 #lv #L #_ #Hlv1 #IH #gv2 #Hgv #lv2 #Hlv
  /3 width=3 by veq_trans/
]
qed.
