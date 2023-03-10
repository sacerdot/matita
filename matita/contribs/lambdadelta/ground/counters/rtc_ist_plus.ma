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
include "ground/counters/rtc_plus.ma".
include "ground/counters/rtc_ist.ma".

(* T-BOUND RT-TRANSITION COUNTERS *******************************************)

(* Constructions with rtc_plus **********************************************)

lemma rtc_ist_plus (n1) (n2) (c1) (c2): šāØn1,c1ā© ā šāØn2,c2ā© ā šāØn1+n2,c1+c2ā©.
#n1 #n2 #c1 #c2 #H1 #H2 destruct //
qed.

lemma rtc_ist_plus_zero_sn (n) (c1) (c2): šāØš,c1ā© ā šāØn,c2ā© ā šāØn,c1+c2ā©.
#n #c1 #c2 #H1 #H2 >(nplus_zero_sn n)
/2 width=1 by rtc_ist_plus/
qed.

lemma rtc_ist_plus_zero_dx (n) (c1) (c2): šāØn,c1ā© ā šāØš,c2ā© ā šāØn,c1+c2ā©.
/2 width=1 by rtc_ist_plus/ qed.

lemma rtc_ist_succ (n) (c): šāØn,cā© ā šāØān,c+ššā©.
#n #c #H >nplus_unit_dx
/2 width=1 by rtc_ist_plus/
qed.

(* Inversions with rtc_plus *************************************************)

lemma rtc_ist_inv_plus (n) (c1) (c2): šāØn,c1 + c2ā© ā
      āān1,n2. šāØn1,c1ā© & šāØn2,c2ā© & n1 + n2 = n.
#n #c1 #c2 #H
elim (rtc_plus_inv_dx ā¦ H) -H #ri1 #rs1 #ti1 #ts1 #ri2 #rs2 #ti2 #ts2 #H1 #H2 #H3 #H4 #H5 #H6 destruct
elim (eq_inv_nplus_zero ā¦ H1) -H1 #H11 #H12 destruct
elim (eq_inv_nplus_zero ā¦ H2) -H2 #H21 #H22 destruct
elim (eq_inv_nplus_zero ā¦ H3) -H3 #H31 #H32 destruct
/3 width=5 by ex3_2_intro/
qed-.

lemma rtc_ist_inv_plus_zero_dx (n) (c1) (c2): šāØn,c1 + c2ā© ā šāØš,c2ā© ā šāØn,c1ā©.
#n #c1 #c2 #H #H2
elim (rtc_ist_inv_plus ā¦ H) -H #n1 #n2 #Hn1 #Hn2 #H destruct //
qed-.

lemma rtc_ist_inv_plus_unit_dx:
      ān,c1,c2. šāØn,c1 + c2ā© ā šāØš,c2ā© ā
      āām. šāØm,c1ā© & n = ām.
#n #c1 #c2 #H #H2 destruct
elim (rtc_ist_inv_plus ā¦ H) -H #n1 #n2 #Hn1 #Hn2 #H destruct
/2 width=3 by ex2_intro/
qed-.

lemma rtc_ist_inv_plus_zu_dx (n) (c): šāØn,c+ššā© ā ā„.
#n #c #H
elim (rtc_ist_inv_plus ā¦ H) -H #n1 #n2 #_ #H #_
/2 width=2 by rtc_ist_inv_uz/
qed-.
