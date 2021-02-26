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

include "ground/xoa/ex_3_2.ma".
include "ground/counters/rtc_max.ma".
include "ground/counters/rtc_ist.ma".

(* T-BOUND RT-TRANSITION COUNTERS *******************************************)

(* Constructions with rtc_max ***********************************************)

lemma rtc_ist_max (n1) (n2) (c1) (c2): 𝐓❪n1,c1❫ → 𝐓❪n2,c2❫ → 𝐓❪n1∨n2,c1∨c2❫.
#n1 #n2 #c1 #c2 #H1 #H2 destruct //
qed.

lemma rtc_ist_max_zero_sn (n) (c1) (c2): 𝐓❪𝟎,c1❫ → 𝐓❪n,c2❫ → 𝐓❪n,c1∨c2❫.
/2 width=1 by rtc_ist_max/ qed.

lemma rtc_ist_max_zero_dx (n) (c1) (c2): 𝐓❪n,c1❫ → 𝐓❪𝟎,c2❫ → 𝐓❪n,c1∨c2❫.
// qed.

lemma rtc_ist_max_idem_sn (n) (c1) (c2): 𝐓❪n,c1❫ → 𝐓❪n,c2❫ → 𝐓❪n,c1∨c2❫.
#n #c1 #c2 #H1 #H2 >(nmax_idem n) /2 width=1 by rtc_ist_max/
qed.

(* Inversions with rtc_max **************************************************)

lemma rtc_ist_inv_max (n) (c1) (c2): 𝐓❪n,c1 ∨ c2❫ →
      ∃∃n1,n2. 𝐓❪n1,c1❫ & 𝐓❪n2,c2❫ & (n1 ∨ n2) = n.
#n #c1 #c2 #H
elim (rtc_max_inv_dx … H) -H #ri1 #rs1 #ti1 #ts1 #ri2 #rs2 #ti2 #ts2 #H1 #H2 #H3 #H4 #H5 #H6 destruct
elim (eq_inv_nmax_zero … H1) -H1 #H11 #H12 destruct
elim (eq_inv_nmax_zero … H2) -H2 #H21 #H22 destruct
elim (eq_inv_nmax_zero … H3) -H3 #H31 #H32 destruct
/2 width=5 by ex3_2_intro/
qed-.

lemma rtc_ist_inv_zero_max (c1) (c2): 𝐓❪𝟎,c1 ∨ c2❫ → ∧∧ 𝐓❪𝟎,c1❫ & 𝐓❪𝟎,c2❫.
#c1 #c2 #H
elim (rtc_ist_inv_max … H) -H #n1 #n2 #Hn1 #Hn2 #H
elim (eq_inv_nmax_zero … H) -H #H1 #H2 destruct
/2 width=1 by conj/
qed-.

lemma rtc_ist_inv_max_zero_dx (n) (c1) (c2): 𝐓❪n,c1 ∨ c2❫ → 𝐓❪𝟎,c2❫ → 𝐓❪n,c1❫.
#n #c1 #c2 #H #H2
elim (rtc_ist_inv_max … H) -H #n1 #n2 #Hn1 #Hn2 #H destruct //
qed-.
