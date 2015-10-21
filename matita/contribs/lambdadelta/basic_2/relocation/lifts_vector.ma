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

(* GENERIC TERM VECTOR RELOCATION *******************************************)

(* Basic_2A1: includes: liftv_nil liftv_cons *)
inductive liftsv (t:trace) : relation (list term) ≝
| liftsv_nil : liftsv t (◊) (◊)
| liftsv_cons: ∀T1s,T2s,T1,T2.
               ⬆*[t] T1 ≡ T2 → liftsv t T1s T2s →
               liftsv t (T1 @ T1s) (T2 @ T2s)
.

interpretation "generic relocation (vector)"
   'RLiftStar t T1s T2s = (liftsv t T1s T2s).

(* Basic inversion lemmas ***************************************************)

fact liftsv_inv_nil1_aux: ∀X,Y,t. ⬆*[t] X ≡ Y → X = ◊ → Y = ◊.
#X #Y #t * -X -Y //
#T1s #T2s #T1 #T2 #_ #_ #H destruct
qed-.

(* Basic_2A1: includes: liftv_inv_nil1 *)
lemma liftsv_inv_nil1: ∀Y,t. ⬆*[t] ◊ ≡ Y → Y = ◊.
/2 width=5 by liftsv_inv_nil1_aux/ qed-.

fact liftsv_inv_cons1_aux: ∀X,Y,t. ⬆*[t] X ≡ Y →
                           ∀T1,T1s. X = T1 @ T1s →
                           ∃∃T2,T2s. ⬆*[t] T1 ≡ T2 & ⬆*[t] T1s ≡ T2s &
                                     Y = T2 @ T2s.
#X #Y #t * -X -Y
[ #U1 #U1s #H destruct
| #T1s #T2s #T1 #T2 #HT12 #HT12s #U1 #U1s #H destruct /2 width=5 by ex3_2_intro/
]
qed-.

(* Basic_2A1: includes: liftv_inv_cons1 *)
lemma liftsv_inv_cons1: ∀T1,T1s,Y,t. ⬆*[t] T1 @ T1s ≡ Y →
                        ∃∃T2,T2s. ⬆*[t] T1 ≡ T2 & ⬆*[t] T1s ≡ T2s &
                                  Y = T2 @ T2s.
/2 width=3 by liftsv_inv_cons1_aux/ qed-.

fact liftsv_inv_nil2_aux: ∀X,Y,t. ⬆*[t] X ≡ Y → Y = ◊ → X = ◊.
#X #Y #t * -X -Y //
#T1s #T2s #T1 #T2 #_ #_ #H destruct
qed-.

lemma liftsv_inv_nil2: ∀X,t. ⬆*[t] X ≡ ◊ → X = ◊.
/2 width=5 by liftsv_inv_nil2_aux/ qed-.

fact liftsv_inv_cons2_aux: ∀X,Y,t. ⬆*[t] X ≡ Y →
                           ∀T2,T2s. Y = T2 @ T2s →
                           ∃∃T1,T1s. ⬆*[t] T1 ≡ T2 & ⬆*[t] T1s ≡ T2s &
                                     X = T1 @ T1s.
#X #Y #t * -X -Y
[ #U2 #U2s #H destruct
| #T1s #T2s #T1 #T2 #HT12 #HT12s #U2 #U2s #H destruct /2 width=5 by ex3_2_intro/
]
qed-.

lemma liftsv_inv_cons2: ∀X,T2,T2s,t. ⬆*[t] X ≡ T2 @ T2s →
                        ∃∃T1,T1s. ⬆*[t] T1 ≡ T2 & ⬆*[t] T1s ≡ T2s &
                                  X = T1 @ T1s.
/2 width=3 by liftsv_inv_cons2_aux/ qed-.

(* Basic_1: was: lifts1_flat (left to right) *)
lemma lifts_inv_applv1: ∀V1s,U1,T2,t. ⬆*[t] Ⓐ V1s.U1 ≡ T2 →
                        ∃∃V2s,U2. ⬆*[t] V1s ≡ V2s & ⬆*[t] U1 ≡ U2 &
                                  T2 = Ⓐ V2s.U2.
#V1s elim V1s -V1s
[ /3 width=5 by ex3_2_intro, liftsv_nil/
| #V1 #V1s #IHV1s #T1 #X #t #H elim (lifts_inv_flat1 … H) -H
  #V2 #Y #HV12 #HY #H destruct elim (IHV1s … HY) -IHV1s -HY
  #V2s #T2 #HV12s #HT12 #H destruct /3 width=5 by ex3_2_intro, liftsv_cons/
]
qed-.

lemma lifts_inv_applv2: ∀V2s,U2,T1,t. ⬆*[t] T1 ≡ Ⓐ V2s.U2 →
                        ∃∃V1s,U1. ⬆*[t] V1s ≡ V2s & ⬆*[t] U1 ≡ U2 &
                                  T1 = Ⓐ V1s.U1.
#V2s elim V2s -V2s
[ /3 width=5 by ex3_2_intro, liftsv_nil/
| #V2 #V2s #IHV2s #T2 #X #t #H elim (lifts_inv_flat2 … H) -H
  #V1 #Y #HV12 #HY #H destruct elim (IHV2s … HY) -IHV2s -HY
  #V1s #T1 #HV12s #HT12 #H destruct /3 width=5 by ex3_2_intro, liftsv_cons/
]
qed-.

(* Basic properties *********************************************************)

(* Basic_1: was: lifts1_flat (right to left) *)
lemma lifts_applv: ∀V1s,V2s,t. ⬆*[t] V1s ≡ V2s →
                   ∀T1,T2. ⬆*[t] T1 ≡ T2 →
                   ⬆*[t] Ⓐ V1s. T1 ≡ Ⓐ V2s. T2.
#V1s #V2s #t #H elim H -V1s -V2s /3 width=1 by lifts_flat/
qed.

(* Basic_2A1: removed theorems 1: liftv_total *)
(* Basic_1: removed theorems 2: lifts1_nil lifts1_cons *)
