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

(* GENERIC RELOCATION FOR TERMS *********************************************)

(* Main properties **********************************************************)

(* Basic_2A1: includes: lift_inj *)
theorem lifts_inj: ∀t,T1,U. ⬆*[t] T1 ≡ U → ∀T2. ⬆*[t] T2 ≡ U → T1 = T2.
#t #T1 #U #H elim H -t -T1 -U
[ /2 width=2 by lifts_inv_sort2/
| #i1 #j #t #Hi1j #X #HX elim (lifts_inv_lref2 … HX) -HX
  /4 width=4 by at_inj, eq_f/
| /2 width=2 by lifts_inv_gref2/
| #a #I #V1 #V2 #T1 #T2 #t #_ #_ #IHV12 #IHT12 #X #HX elim (lifts_inv_bind2 … HX) -HX
  #V #T #HV1 #HT1 #HX destruct /3 width=1 by eq_f2/
| #I #V1 #V2 #T1 #T2 #t #_ #_ #IHV12 #IHT12 #X #HX elim (lifts_inv_flat2 … HX) -HX
  #V #T #HV1 #HT1 #HX destruct /3 width=1 by eq_f2/
]
qed-.

(* Basic_1: includes: lift_gen_lift *)
(* Basic_2A1: includes: lift_div_le lift_div_be *)
theorem lifts_div: ∀T,T2,t2. ⬆*[t2] T2 ≡ T → ∀T1,t. ⬆*[t] T1 ≡ T →
                   ∀t1. t2 ⊚ t1 ≡ t → ⬆*[t1] T1 ≡ T2.
#T #T2 #t2 #H elim H -T -T2 -t2
[ #k #t2 #T1 #t #H >(lifts_inv_sort2 … H) -T1 //
| #i2 #i #t2 #Hi2 #T1 #t #H #t1 #Ht21 elim (lifts_inv_lref2 … H) -H
  #i1 #Hi1 #H destruct /3 width=6 by lifts_lref, after_fwd_at1/
| #p #t2 #T1 #t #H >(lifts_inv_gref2 … H) -T1 //
| #a #I #W2 #W #U2 #U #t2 #_ #_ #IHW #IHU #T1 #t #H
  elim (lifts_inv_bind2 … H) -H #W1 #U1 #HW1 #HU1 #H destruct
  /4 width=3 by lifts_bind, after_true/
| #I #W2 #W #U2 #U #t2 #_ #_ #IHW #IHU #T1 #t #H
  elim (lifts_inv_flat2 … H) -H #W1 #U1 #HW1 #HU1 #H destruct
  /3 width=3 by lifts_flat/
]
qed-.

(* Basic_2A1: includes: lift_mono *)
theorem lifts_mono: ∀t,T,U1. ⬆*[t] T ≡ U1 → ∀U2. ⬆*[t] T ≡ U2 → U1 = U2.
#t #T #U1 #H elim H -t -T -U1
[ /2 width=2 by lifts_inv_sort1/
| #i1 #j #t #Hi1j #X #HX elim (lifts_inv_lref1 … HX) -HX
  /4 width=4 by at_mono, eq_f/
| /2 width=2 by lifts_inv_gref1/
| #a #I #V1 #V2 #T1 #T2 #t #_ #_ #IHV12 #IHT12 #X #HX elim (lifts_inv_bind1 … HX) -HX
  #V #T #HV1 #HT1 #HX destruct /3 width=1 by eq_f2/
| #I #V1 #V2 #T1 #T2 #t #_ #_ #IHV12 #IHT12 #X #HX elim (lifts_inv_flat1 … HX) -HX
  #V #T #HV1 #HT1 #HX destruct /3 width=1 by eq_f2/
]
qed-.

(* Basic_1: was: lift1_lift1 (left to right) *)
(* Basic_1: includes: lift_free (left to right) lift_d lift1_xhg (right to left) lift1_free (right to left) *)
(* Basic_2A1: includes: lift_trans_be lift_trans_le lift_trans_ge lifts_lift_trans_le lifts_lift_trans *)
theorem lifts_trans: ∀T1,T,t1. ⬆*[t1] T1 ≡ T → ∀T2,t2. ⬆*[t2] T ≡ T2 →
                     ∀t. t2 ⊚ t1 ≡ t → ⬆*[t] T1 ≡ T2.
#T1 #T #t1 #H elim H -T1 -T -t1
[ #k #t1 #T2 #t2 #H >(lifts_inv_sort1 … H) -T2 //
| #i1 #i #t1 #Hi1 #T2 #t2 #H #t #Ht21 elim (lifts_inv_lref1 … H) -H
  #i2 #Hi2 #H destruct /3 width=6 by lifts_lref, after_fwd_at/
| #p #t1 #T2 #t2 #H >(lifts_inv_gref1 … H) -T2 //
| #a #I #W1 #W #U1 #U #t1 #_ #_ #IHW #IHU #T2 #t2 #H
  elim (lifts_inv_bind1 … H) -H #W2 #U2 #HW2 #HU2 #H destruct
  /4 width=3 by lifts_bind, after_true/
| #I #W1 #W #U1 #U #t1 #_ #_ #IHW #IHU #T2 #t2 #H
  elim (lifts_inv_flat1 … H) -H #W2 #U2 #HW2 #HU2 #H destruct
  /3 width=3 by lifts_flat/
]
qed-.

(* Basic_2A1: includes: lift_conf_O1 lift_conf_be *)
theorem lifts_conf: ∀T,T1,t1. ⬆*[t1] T ≡ T1 → ∀T2,t. ⬆*[t] T ≡ T2 →
                    ∀t2. t2 ⊚ t1 ≡ t → ⬆*[t2] T1 ≡ T2.
#T #T1 #t1 #H elim H -T -T1 -t1
[ #k #t1 #T2 #t #H >(lifts_inv_sort1 … H) -T2 //
| #i #i1 #t1 #Hi1 #T2 #t #H #t2 #Ht21 elim (lifts_inv_lref1 … H) -H
  #i2 #Hi2 #H destruct /3 width=6 by lifts_lref, after_fwd_at2/
| #p #t1 #T2 #t #H >(lifts_inv_gref1 … H) -T2 //
| #a #I #W #W1 #U #U1 #t1 #_ #_ #IHW #IHU #T2 #t #H
  elim (lifts_inv_bind1 … H) -H #W2 #U2 #HW2 #HU2 #H destruct
  /4 width=3 by lifts_bind, after_true/
| #I #W #W1 #U #U1 #t1 #_ #_ #IHW #IHU #T2 #t #H
  elim (lifts_inv_flat1 … H) -H #W2 #U2 #HW2 #HU2 #H destruct
  /3 width=3 by lifts_flat/
]
qed-.
