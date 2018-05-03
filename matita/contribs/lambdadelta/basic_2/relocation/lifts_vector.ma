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

include "basic_2/syntax/term_vector.ma".
include "basic_2/relocation/lifts.ma".

(* GENERIC RELOCATION FOR TERM VECTORS *************************************)

(* Basic_2A1: includes: liftv_nil liftv_cons *)
inductive liftsv (f:rtmap): relation (list term) ≝
| liftsv_nil : liftsv f (◊) (◊)
| liftsv_cons: ∀T1s,T2s,T1,T2.
               ⬆*[f] T1 ≘ T2 → liftsv f T1s T2s →
               liftsv f (T1 ⨮ T1s) (T2 ⨮ T2s)
.

interpretation "uniform relocation (term vector)"
   'RLiftStar i T1s T2s = (liftsv (uni i) T1s T2s).

interpretation "generic relocation (term vector)"
   'RLiftStar f T1s T2s = (liftsv f T1s T2s).

(* Basic inversion lemmas ***************************************************)

fact liftsv_inv_nil1_aux: ∀f,X,Y. ⬆*[f] X ≘ Y → X = ◊ → Y = ◊.
#f #X #Y * -X -Y //
#T1s #T2s #T1 #T2 #_ #_ #H destruct
qed-.

(* Basic_2A1: includes: liftv_inv_nil1 *)
lemma liftsv_inv_nil1: ∀f,Y. ⬆*[f] ◊ ≘ Y → Y = ◊.
/2 width=5 by liftsv_inv_nil1_aux/ qed-.

fact liftsv_inv_cons1_aux: ∀f:rtmap. ∀X,Y. ⬆*[f] X ≘ Y →
                           ∀T1,T1s. X = T1 ⨮ T1s →
                           ∃∃T2,T2s. ⬆*[f] T1 ≘ T2 & ⬆*[f] T1s ≘ T2s &
                                     Y = T2 ⨮ T2s.
#f #X #Y * -X -Y
[ #U1 #U1s #H destruct
| #T1s #T2s #T1 #T2 #HT12 #HT12s #U1 #U1s #H destruct /2 width=5 by ex3_2_intro/
]
qed-.

(* Basic_2A1: includes: liftv_inv_cons1 *)
lemma liftsv_inv_cons1: ∀f:rtmap. ∀T1,T1s,Y. ⬆*[f] T1 ⨮ T1s ≘ Y →
                        ∃∃T2,T2s. ⬆*[f] T1 ≘ T2 & ⬆*[f] T1s ≘ T2s &
                                  Y = T2 ⨮ T2s.
/2 width=3 by liftsv_inv_cons1_aux/ qed-.

fact liftsv_inv_nil2_aux: ∀f,X,Y. ⬆*[f] X ≘ Y → Y = ◊ → X = ◊.
#f #X #Y * -X -Y //
#T1s #T2s #T1 #T2 #_ #_ #H destruct
qed-.

lemma liftsv_inv_nil2: ∀f,X. ⬆*[f] X ≘ ◊ → X = ◊.
/2 width=5 by liftsv_inv_nil2_aux/ qed-.

fact liftsv_inv_cons2_aux: ∀f:rtmap. ∀X,Y. ⬆*[f] X ≘ Y →
                           ∀T2,T2s. Y = T2 ⨮ T2s →
                           ∃∃T1,T1s. ⬆*[f] T1 ≘ T2 & ⬆*[f] T1s ≘ T2s &
                                     X = T1 ⨮ T1s.
#f #X #Y * -X -Y
[ #U2 #U2s #H destruct
| #T1s #T2s #T1 #T2 #HT12 #HT12s #U2 #U2s #H destruct /2 width=5 by ex3_2_intro/
]
qed-.

lemma liftsv_inv_cons2: ∀f:rtmap. ∀X,T2,T2s. ⬆*[f] X ≘ T2 ⨮ T2s →
                        ∃∃T1,T1s. ⬆*[f] T1 ≘ T2 & ⬆*[f] T1s ≘ T2s &
                                  X = T1 ⨮ T1s.
/2 width=3 by liftsv_inv_cons2_aux/ qed-.

(* Basic_1: was: lifts1_flat (left to right) *)
lemma lifts_inv_applv1: ∀f:rtmap. ∀V1s,U1,T2. ⬆*[f] Ⓐ V1s.U1 ≘ T2 →
                        ∃∃V2s,U2. ⬆*[f] V1s ≘ V2s & ⬆*[f] U1 ≘ U2 &
                                  T2 = Ⓐ V2s.U2.
#f #V1s elim V1s -V1s
[ /3 width=5 by ex3_2_intro, liftsv_nil/
| #V1 #V1s #IHV1s #T1 #X #H elim (lifts_inv_flat1 … H) -H
  #V2 #Y #HV12 #HY #H destruct elim (IHV1s … HY) -IHV1s -HY
  #V2s #T2 #HV12s #HT12 #H destruct /3 width=5 by ex3_2_intro, liftsv_cons/
]
qed-.

lemma lifts_inv_applv2: ∀f:rtmap. ∀V2s,U2,T1. ⬆*[f] T1 ≘ Ⓐ V2s.U2 →
                        ∃∃V1s,U1. ⬆*[f] V1s ≘ V2s & ⬆*[f] U1 ≘ U2 &
                                  T1 = Ⓐ V1s.U1.
#f #V2s elim V2s -V2s
[ /3 width=5 by ex3_2_intro, liftsv_nil/
| #V2 #V2s #IHV2s #T2 #X #H elim (lifts_inv_flat2 … H) -H
  #V1 #Y #HV12 #HY #H destruct elim (IHV2s … HY) -IHV2s -HY
  #V1s #T1 #HV12s #HT12 #H destruct /3 width=5 by ex3_2_intro, liftsv_cons/
]
qed-.

(* Basic properties *********************************************************)

(* Basic_2A1: includes: liftv_total *)
lemma liftsv_total: ∀f. ∀T1s:list term. ∃T2s. ⬆*[f] T1s ≘ T2s.
#f #T1s elim T1s -T1s
[ /2 width=2 by liftsv_nil, ex_intro/
| #T1 #T1s * #T2s #HT12s
  elim (lifts_total T1 f) /3 width=2 by liftsv_cons, ex_intro/
]
qed-.

(* Basic_1: was: lifts1_flat (right to left) *)
lemma lifts_applv: ∀f:rtmap. ∀V1s,V2s. ⬆*[f] V1s ≘ V2s →
                   ∀T1,T2. ⬆*[f] T1 ≘ T2 →
                   ⬆*[f] Ⓐ V1s.T1 ≘ Ⓐ V2s.T2.
#f #V1s #V2s #H elim H -V1s -V2s /3 width=1 by lifts_flat/
qed.

lemma liftsv_split_trans: ∀f,T1s,T2s. ⬆*[f] T1s ≘ T2s →
                          ∀f1,f2. f2 ⊚ f1 ≘ f →
                          ∃∃Ts. ⬆*[f1] T1s ≘ Ts & ⬆*[f2] Ts ≘ T2s.
#f #T1s #T2s #H elim H -T1s -T2s
[ /2 width=3 by liftsv_nil, ex2_intro/
| #T1s #T2s #T1 #T2 #HT12 #_ #IH #f1 #f2 #Hf
  elim (IH … Hf) -IH
  elim (lifts_split_trans … HT12 … Hf) -HT12 -Hf
  /3 width=5 by liftsv_cons, ex2_intro/
]
qed-.

(* Basic_1: removed theorems 2: lifts1_nil lifts1_cons *)
