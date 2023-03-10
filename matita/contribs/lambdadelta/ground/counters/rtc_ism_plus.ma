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
include "ground/counters/rtc_ism.ma".

(* T-BOUND RT-TRANSITION COUNTERS *******************************************)

(* Constructions with rtc_plus **********************************************)

lemma rtc_ism_plus (n1) (n2) (c1) (c2):  šāØn1,c1ā© ā šāØn2,c2ā© ā šāØn1+n2,c1+c2ā©.
#n1 #n2 #c1 #c2 * #ri1 #rs1 #H1 * #ri2 #rs2 #H2 destruct
/2 width=3 by ex1_2_intro/
qed.

lemma rtc_ism_plus_zero_sn (n) (c1) (c2): šāØš,c1ā© ā šāØn,c2ā© ā šāØn,c1+c2ā©.
#n #c1 #c2 #H1 #H2 >(nplus_zero_sn n) /2 width=1 by rtc_ism_plus/
qed.

lemma rtc_ism_plus_zero_dx (n) (c1) (c2): šāØn,c1ā© ā šāØš,c2ā© ā šāØn,c1+c2ā©.
/2 width=1 by rtc_ism_plus/ qed.

lemma rtc_ism_succ (n) (c): šāØn,cā© ā šāØān,c+ššā©.
#n #c #H >nplus_unit_dx
/2 width=1 by rtc_ism_plus/
qed.

(* Inversions with rtc_plus *************************************************)

lemma rtc_ism_inv_plus (n) (c1) (c2): šāØn,c1 + c2ā© ā
      āān1,n2. šāØn1,c1ā© & šāØn2,c2ā© & n1 + n2 = n.
#n #c1 #c2 * #ri #rs #H
elim (rtc_plus_inv_dx ā¦ H) -H #ri1 #rs1 #ti1 #ts1 #ri2 #rs2 #ti2 #ts2 #_ #_ #H1 #H2 #H3 #H4
elim (eq_inv_nplus_zero ā¦ H1) -H1 /3 width=5 by ex3_2_intro, ex1_2_intro/
qed-.

lemma rtc_ism_inv_plus_zero_dx (n) (c1) (c2): šāØn,c1 + c2ā© ā šāØš,c2ā© ā šāØn,c1ā©.
#n #c1 #c2 #H #H2
elim (rtc_ism_inv_plus ā¦ H) -H #n1 #n2 #Hn1 #Hn2 #H destruct
lapply (rtc_ism_inj ā¦ Hn2 H2) -c2 #H destruct //
qed-.

lemma rtc_ism_inv_plus_unit_dx (n) (c1) (c2): šāØn,c1 + c2ā© ā šāØš,c2ā© ā
      āām. šāØm,c1ā© & n = ām.
#n #c1 #c2 #H #H2
elim (rtc_ism_inv_plus ā¦ H) -H #n1 #n2 #Hn1 #Hn2 #H destruct
lapply (rtc_ism_inj ā¦ Hn2 H2) -c2 #H destruct
/2 width=3 by ex2_intro/
qed-.
