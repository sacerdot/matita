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

include "ground_2/xoa/ex_3_2.ma".
include "ground_2/steps/rtc_plus.ma".
include "ground_2/steps/rtc_ist.ma".

(* RT-TRANSITION COUNTER ****************************************************)

(* Properties with test for t-transition counter ****************************)

lemma ist_plus: ∀n1,n2,c1,c2. 𝐓❪n1,c1❫ → 𝐓❪n2,c2❫ → 𝐓❪n1+n2,c1+c2❫.
#n1 #n2 #c1 #c2 #H1 #H2 destruct //
qed.

lemma ist_plus_O1: ∀n,c1,c2. 𝐓❪0,c1❫ → 𝐓❪n,c2❫ → 𝐓❪n,c1+c2❫.
/2 width=1 by ist_plus/ qed.

lemma ist_plus_O2: ∀n,c1,c2. 𝐓❪n,c1❫ → 𝐓❪0,c2❫ → 𝐓❪n,c1+c2❫.
#n #c1 #c2 #H1 #H2 >(plus_n_O n) /2 width=1 by ist_plus/
qed.

lemma ist_succ: ∀n,c. 𝐓❪n,c❫ → 𝐓❪↑n,c+𝟘𝟙❫.
/2 width=1 by ist_plus/ qed.

(* Inversion properties with test for constrained rt-transition counter *****)

lemma ist_inv_plus:
      ∀n,c1,c2. 𝐓❪n,c1 + c2❫ →
      ∃∃n1,n2. 𝐓❪n1,c1❫ & 𝐓❪n2,c2❫ & n1 + n2 = n.
#n #c1 #c2 #H
elim (plus_inv_dx … H) -H #ri1 #rs1 #ti1 #ts1 #ri2 #rs2 #ti2 #ts2 #H1 #H2 #H3 #H4 #H5 #H6 destruct
elim (plus_inv_O3 … H1) -H1 #H11 #H12 destruct
elim (plus_inv_O3 … H2) -H2 #H21 #H22 destruct
elim (plus_inv_O3 … H3) -H3 #H31 #H32 destruct
/3 width=5 by ex3_2_intro/
qed-.

lemma ist_inv_plus_O_dx: ∀n,c1,c2. 𝐓❪n,c1 + c2❫ → 𝐓❪0,c2❫ → 𝐓❪n,c1❫.
#n #c1 #c2 #H #H2
elim (ist_inv_plus … H) -H #n1 #n2 #Hn1 #Hn2 #H destruct //
qed-.

lemma ist_inv_plus_SO_dx:
      ∀n,c1,c2. 𝐓❪n,c1 + c2❫ → 𝐓❪1,c2❫ →
      ∃∃m. 𝐓❪m,c1❫ & n = ↑m.
#n #c1 #c2 #H #H2 destruct
elim (ist_inv_plus … H) -H #n1 #n2 #Hn1 #Hn2 #H destruct
/2 width=3 by ex2_intro/
qed-.

lemma ist_inv_plus_10_dx: ∀n,c. 𝐓❪n,c+𝟙𝟘❫ → ⊥.
#n #c #H
elim (ist_inv_plus … H) -H #n1 #n2 #_ #H #_
/2 width=2 by ist_inv_10/
qed-.
