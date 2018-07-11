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

include "apps_2/notation/models/roplus_5.ma".
include "static_2/syntax/lenv.ma".
include "apps_2/models/veq.ma".

(* MULTIPLE LIFT FOR MODEL EVALUATIONS **************************************)

inductive vlifts (M) (gv) (lv): relation2 lenv (evaluation M) ≝
| vlifts_atom: vlifts M gv lv (⋆) lv
| vlifts_abbr: ∀v,d,K,V. vlifts M gv lv K v → ⟦V⟧[gv, v] = d → vlifts M gv lv (K.ⓓV) (⫯[0←d]v)
| vlifts_abst: ∀v,d,K,V. vlifts M gv lv K v → vlifts M gv lv (K.ⓛV) (⫯[0←d]v)
| vlifts_unit: ∀v,d,I,K. vlifts M gv lv K v → vlifts M gv lv (K.ⓤ{I}) (⫯[0←d]v)
| vlifts_repl: ∀v1,v2,L. vlifts M gv lv L v1 → v1 ≗ v2 → vlifts M gv lv L v2
.

interpretation "multiple lift (model evaluation)"
   'ROPlus M gv L lv v  = (vlifts M gv lv L v).

(* Basic inversion lemmas ***************************************************)

fact vlifts_inv_atom_aux (M) (gv) (lv): is_model M →
                                        ∀v,L. L ⨁{M}[gv] lv ≘ v →
                                        ⋆ = L → lv ≗ v.
#M #gv #lv #HM #v #L #H elim H -v -L
[ #_ /2 width=1 by veq_refl/
| #v #d #K #V #_ #_ #_ #H destruct
| #v #d #K #V #_ #_ #H destruct
| #v #d #I #K #_ #_ #H destruct
| #v1 #v2 #L #_ #Hv12 #IH #H destruct
  /3 width=3 by veq_trans/ 
]
qed-.

lemma vlifts_inv_atom (M) (gv) (lv): is_model M →
                                     ∀v. ⋆ ⨁{M}[gv] lv ≘ v → lv ≗ v.
/2 width=4 by vlifts_inv_atom_aux/ qed-.

fact vlifts_inv_abbr_aux (M) (gv) (lv): is_model M →
                                        ∀y,L. L ⨁{M}[gv] lv ≘ y →
                                        ∀K,V. K.ⓓV = L →
                                        ∃∃v. K ⨁[gv] lv ≘ v & ⫯[0←⟦V⟧[gv, v]]v ≗ y.
#M #gv #lv #HM #y #L #H elim H -y -L
[ #Y #X #H destruct
| #v #d #K #V #Hv #Hd #_ #Y #X #H destruct
  /3 width=3 by veq_refl, ex2_intro/
| #v #d #K #V #_ #_ #Y #X #H destruct
| #v #d #I #K #_ #_ #Y #X #H destruct
| #v1 #v2 #L #_ #Hv12 #IH #Y #X #H destruct
  elim IH -IH [|*: // ] #v #Hv #Hv1
  /3 width=5 by veq_trans, ex2_intro/
]
qed-.

lemma vlifts_inv_abbr (M) (gv) (lv): is_model M →
                                     ∀y,K,V. K.ⓓV ⨁{M}[gv] lv ≘ y →
                                     ∃∃v. K ⨁[gv] lv ≘ v & ⫯[0←⟦V⟧[gv, v]]v ≗ y.
/2 width=3 by vlifts_inv_abbr_aux/ qed-.

fact vlifts_inv_abst_aux (M) (gv) (lv): is_model M →
                                        ∀y,L. L ⨁{M}[gv] lv ≘ y →
                                        ∀K,W. K.ⓛW = L →
                                        ∃∃v,d. K ⨁[gv] lv ≘ v & ⫯[0←d]v ≗ y.
#M #gv #lv #HM #y #L #H elim H -y -L
[ #Y #X #H destruct
| #v #d #K #V #_ #_ #_ #Y #X #H destruct
| #v #d #K #V #Hv #_ #Y #X #H destruct
  /3 width=4 by veq_refl, ex2_2_intro/
| #v #d #I #K #_ #_ #Y #X #H destruct
| #v1 #v2 #L #_ #Hv12 #IH #Y #X #H destruct
  elim IH -IH [|*: // ] #v #d #Hv #Hv1
  /3 width=6 by veq_trans, ex2_2_intro/
]
qed-.

lemma vlifts_inv_abst (M) (gv) (lv): is_model M →
                                     ∀y,K,W. K.ⓛW ⨁{M}[gv] lv ≘ y →
                                     ∃∃v,d. K ⨁[gv] lv ≘ v & ⫯[0←d]v ≗ y.
/2 width=4 by vlifts_inv_abst_aux/ qed-.

fact vlifts_inv_unit_aux (M) (gv) (lv): is_model M →
                                        ∀y,L. L ⨁{M}[gv] lv ≘ y →
                                        ∀I,K. K.ⓤ{I} = L →
                                        ∃∃v,d. K ⨁[gv] lv ≘ v & ⫯[0←d]v ≗ y.
#M #gv #lv #HM #y #L #H elim H -y -L
[ #Z #Y #H destruct
| #v #d #K #V #_ #_ #_ #Z #Y #H destruct
| #v #d #K #V #_ #_ #Z #Y #H destruct
| #v #d #I #K #Hv #_ #Z #Y #H destruct
  /3 width=4 by veq_refl, ex2_2_intro/
| #v1 #v2 #L #_ #Hv12 #IH #Z #Y #H destruct
  elim IH -IH [|*: // ] #v #d #Hv #Hv1
  /3 width=6 by veq_trans, ex2_2_intro/
]
qed-.

lemma vlifts_inv_unit (M) (gv) (lv): is_model M →
                                     ∀y,I,K. K.ⓤ{I} ⨁{M}[gv] lv ≘ y →
                                     ∃∃v,d. K ⨁[gv] lv ≘ v & ⫯[0←d]v ≗ y.
/2 width=4 by vlifts_inv_unit_aux/ qed-.

(* Basic forward lemmas *****************************************************)

lemma vlifts_fwd_bind (M) (gv) (lv): is_model M →
                                     ∀y,I,K. K.ⓘ{I} ⨁{M}[gv] lv ≘ y →
                                     ∃∃v,d. K ⨁[gv] lv ≘ v & ⫯[0←d]v ≗ y.
#M #gv #lv #HM #y * [ #I | * #V ] #L #H
[ /2 width=2 by vlifts_inv_unit/
| elim (vlifts_inv_abbr … H) // -H #v #HL #Hv
  /2 width=4 by ex2_2_intro/
| /2 width=2 by vlifts_inv_abst/
]
qed-.
