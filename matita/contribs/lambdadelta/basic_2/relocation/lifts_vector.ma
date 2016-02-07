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

include "basic_2/grammar/term_vector.ma".
include "basic_2/relocation/lifts.ma".

(* GENERIC RELOCATION FOR TERM VECTORS *************************************)

(* Basic_2A1: includes: liftv_nil liftv_cons *)
inductive liftsv (f): relation (list term) ≝
| liftsv_nil : liftsv f (◊) (◊)
| liftsv_cons: ∀T1c,T2c,T1,T2.
               ⬆*[f] T1 ≡ T2 → liftsv f T1c T2c →
               liftsv f (T1 @ T1c) (T2 @ T2c)
.

interpretation "generic relocation (vector)"
   'RLiftStar f T1c T2c = (liftsv f T1c T2c).

(* Basic inversion lemmas ***************************************************)

fact liftsv_inv_nil1_aux: ∀X,Y,f. ⬆*[f] X ≡ Y → X = ◊ → Y = ◊.
#X #Y #f * -X -Y //
#T1c #T2c #T1 #T2 #_ #_ #H destruct
qed-.

(* Basic_2A1: includes: liftv_inv_nil1 *)
lemma liftsv_inv_nil1: ∀Y,f. ⬆*[f] ◊ ≡ Y → Y = ◊.
/2 width=5 by liftsv_inv_nil1_aux/ qed-.

fact liftsv_inv_cons1_aux: ∀X,Y,f. ⬆*[f] X ≡ Y →
                           ∀T1,T1c. X = T1 @ T1c →
                           ∃∃T2,T2c. ⬆*[f] T1 ≡ T2 & ⬆*[f] T1c ≡ T2c &
                                     Y = T2 @ T2c.
#X #Y #f * -X -Y
[ #U1 #U1c #H destruct
| #T1c #T2c #T1 #T2 #HT12 #HT12c #U1 #U1c #H destruct /2 width=5 by ex3_2_intro/
]
qed-.

(* Basic_2A1: includes: liftv_inv_cons1 *)
lemma liftsv_inv_cons1: ∀T1,T1c,Y,f. ⬆*[f] T1 @ T1c ≡ Y →
                        ∃∃T2,T2c. ⬆*[f] T1 ≡ T2 & ⬆*[f] T1c ≡ T2c &
                                  Y = T2 @ T2c.
/2 width=3 by liftsv_inv_cons1_aux/ qed-.

fact liftsv_inv_nil2_aux: ∀X,Y,f. ⬆*[f] X ≡ Y → Y = ◊ → X = ◊.
#X #Y #f * -X -Y //
#T1c #T2c #T1 #T2 #_ #_ #H destruct
qed-.

lemma liftsv_inv_nil2: ∀X,f. ⬆*[f] X ≡ ◊ → X = ◊.
/2 width=5 by liftsv_inv_nil2_aux/ qed-.

fact liftsv_inv_cons2_aux: ∀X,Y,f. ⬆*[f] X ≡ Y →
                           ∀T2,T2c. Y = T2 @ T2c →
                           ∃∃T1,T1c. ⬆*[f] T1 ≡ T2 & ⬆*[f] T1c ≡ T2c &
                                     X = T1 @ T1c.
#X #Y #f * -X -Y
[ #U2 #U2c #H destruct
| #T1c #T2c #T1 #T2 #HT12 #HT12c #U2 #U2c #H destruct /2 width=5 by ex3_2_intro/
]
qed-.

lemma liftsv_inv_cons2: ∀X,T2,T2c,f. ⬆*[f] X ≡ T2 @ T2c →
                        ∃∃T1,T1c. ⬆*[f] T1 ≡ T2 & ⬆*[f] T1c ≡ T2c &
                                  X = T1 @ T1c.
/2 width=3 by liftsv_inv_cons2_aux/ qed-.

(* Basic_1: was: lifts1_flat (left to right) *)
lemma lifts_inv_applv1: ∀V1c,U1,T2,f. ⬆*[f] Ⓐ V1c.U1 ≡ T2 →
                        ∃∃V2c,U2. ⬆*[f] V1c ≡ V2c & ⬆*[f] U1 ≡ U2 &
                                  T2 = Ⓐ V2c.U2.
#V1c elim V1c -V1c
[ /3 width=5 by ex3_2_intro, liftsv_nil/
| #V1 #V1c #IHV1c #T1 #X #f #H elim (lifts_inv_flat1 … H) -H
  #V2 #Y #HV12 #HY #H destruct elim (IHV1c … HY) -IHV1c -HY
  #V2c #T2 #HV12c #HT12 #H destruct /3 width=5 by ex3_2_intro, liftsv_cons/
]
qed-.

lemma lifts_inv_applv2: ∀V2c,U2,T1,f. ⬆*[f] T1 ≡ Ⓐ V2c.U2 →
                        ∃∃V1c,U1. ⬆*[f] V1c ≡ V2c & ⬆*[f] U1 ≡ U2 &
                                  T1 = Ⓐ V1c.U1.
#V2c elim V2c -V2c
[ /3 width=5 by ex3_2_intro, liftsv_nil/
| #V2 #V2c #IHV2c #T2 #X #f #H elim (lifts_inv_flat2 … H) -H
  #V1 #Y #HV12 #HY #H destruct elim (IHV2c … HY) -IHV2c -HY
  #V1c #T1 #HV12c #HT12 #H destruct /3 width=5 by ex3_2_intro, liftsv_cons/
]
qed-.

(* Basic properties *********************************************************)

(* Basic_2A1: includes: liftv_total *)
lemma liftsv_total: ∀f. ∀T1c:list term. ∃T2c. ⬆*[f] T1c ≡ T2c.
#f #T1c elim T1c -T1c
[ /2 width=2 by liftsv_nil, ex_intro/
| #T1 #T1c * #T2c #HT12c
  elim (lifts_total T1 f) /3 width=2 by liftsv_cons, ex_intro/
]
qed-.

(* Basic_1: was: lifts1_flat (right to left) *)
lemma lifts_applv: ∀V1c,V2c,f. ⬆*[f] V1c ≡ V2c →
                   ∀T1,T2. ⬆*[f] T1 ≡ T2 →
                   ⬆*[f] Ⓐ V1c. T1 ≡ Ⓐ V2c. T2.
#V1c #V2c #f #H elim H -V1c -V2c /3 width=1 by lifts_flat/
qed.

(* Basic_1: removed theorems 2: lifts1_nil lifts1_cons *)
