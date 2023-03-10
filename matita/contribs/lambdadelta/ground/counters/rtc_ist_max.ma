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

lemma rtc_ist_max (n1) (n2) (c1) (c2): đâšn1,c1â© â đâšn2,c2â© â đâšn1âšn2,c1âšc2â©.
#n1 #n2 #c1 #c2 #H1 #H2 destruct //
qed.

lemma rtc_ist_max_zero_sn (n) (c1) (c2): đâšđ,c1â© â đâšn,c2â© â đâšn,c1âšc2â©.
/2 width=1 by rtc_ist_max/ qed.

lemma rtc_ist_max_zero_dx (n) (c1) (c2): đâšn,c1â© â đâšđ,c2â© â đâšn,c1âšc2â©.
// qed.

lemma rtc_ist_max_idem_sn (n) (c1) (c2): đâšn,c1â© â đâšn,c2â© â đâšn,c1âšc2â©.
#n #c1 #c2 #H1 #H2 >(nmax_idem n) /2 width=1 by rtc_ist_max/
qed.

(* Inversions with rtc_max **************************************************)

lemma rtc_ist_inv_max (n) (c1) (c2): đâšn,c1 âš c2â© â
      âân1,n2. đâšn1,c1â© & đâšn2,c2â© & (n1 âš n2) = n.
#n #c1 #c2 #H
elim (rtc_max_inv_dx âŠ H) -H #ri1 #rs1 #ti1 #ts1 #ri2 #rs2 #ti2 #ts2 #H1 #H2 #H3 #H4 #H5 #H6 destruct
elim (eq_inv_nmax_zero âŠ H1) -H1 #H11 #H12 destruct
elim (eq_inv_nmax_zero âŠ H2) -H2 #H21 #H22 destruct
elim (eq_inv_nmax_zero âŠ H3) -H3 #H31 #H32 destruct
/2 width=5 by ex3_2_intro/
qed-.

lemma rtc_ist_inv_zero_max (c1) (c2): đâšđ,c1 âš c2â© â â§â§ đâšđ,c1â© & đâšđ,c2â©.
#c1 #c2 #H
elim (rtc_ist_inv_max âŠ H) -H #n1 #n2 #Hn1 #Hn2 #H
elim (eq_inv_nmax_zero âŠ H) -H #H1 #H2 destruct
/2 width=1 by conj/
qed-.

lemma rtc_ist_inv_max_zero_dx (n) (c1) (c2): đâšn,c1 âš c2â© â đâšđ,c2â© â đâšn,c1â©.
#n #c1 #c2 #H #H2
elim (rtc_ist_inv_max âŠ H) -H #n1 #n2 #Hn1 #Hn2 #H destruct //
qed-.
