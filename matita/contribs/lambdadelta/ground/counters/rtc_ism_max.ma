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
include "ground/counters/rtc_ism.ma".

(* T-BOUND RT-TRANSITION COUNTERS *******************************************)

(* Constructions with rtc_max ***********************************************)

lemma rtc_ism_max (n1) (n2) (c1) (c2): đâšn1,c1â© â đâšn2,c2â© â đâšn1âšn2,c1âšc2â©.
#n1 #n2 #c1 #c2 * #ri1 #rs1 #H1 * #ri2 #rs2 #H2 destruct
/2 width=3 by ex1_2_intro/
qed.

lemma rtc_ism_max_zero_sn (n) (c1) (c2): đâšđ,c1â© â đâšn,c2â© â đâšn,c1âšc2â©.
/2 width=1 by rtc_ism_max/ qed.

lemma rtc_ism_max_zero_dx (n) (c1) (c2): đâšn,c1â© â đâšđ,c2â© â đâšn,c1âšc2â©.
#n #c1 #c2 #H1 #H2 >(nmax_zero_dx n) /2 width=1 by rtc_ism_max/
qed.

lemma rtc_ism_max_idem_sn (n) (c1) (c2): đâšn,c1â© â đâšn,c2â© â đâšn,c1âšc2â©.
#n #c1 #c2 #H1 #H2 >(nmax_idem n) /2 width=1 by rtc_ism_max/
qed.

(* Inversions with rtc_max **************************************************)

lemma rtc_ism_inv_max (n) (c1) (c2): đâšn,c1 âš c2â© â
      âân1,n2. đâšn1,c1â© & đâšn2,c2â© & (n1 âš n2) = n.
#n #c1 #c2 * #ri #rs #H
elim (rtc_max_inv_dx âŠ H) -H #ri1 #rs1 #ti1 #ts1 #ri2 #rs2 #ti2 #ts2 #_ #_ #H1 #H2 #H3 #H4
elim (eq_inv_nmax_zero âŠ H1) -H1 /3 width=5 by ex3_2_intro, ex1_2_intro/
qed-.

lemma rtc_isr_inv_max (c1) (c2): đâšđ,c1 âš c2â© â â§â§ đâšđ,c1â© & đâšđ,c2â©.
#c1 #c2 #H
elim (rtc_ism_inv_max âŠ H) -H #n1 #n2 #Hn1 #Hn2 #H
elim (eq_inv_nmax_zero âŠ H) -H #H1 #H2 destruct
/2 width=1 by conj/
qed-.

lemma rtc_ism_inv_max_zero_dx (n) (c1) (c2): đâšn,c1 âš c2â© â đâšđ,c2â© â đâšn,c1â©.
#n #c1 #c2 #H #H2
elim (rtc_ism_inv_max âŠ H) -H #n1 #n2 #Hn1 #Hn2 #H destruct
lapply (rtc_ism_inj âŠ Hn2 H2) -c2 #H destruct //
qed-.

lemma rtc_ism_inv_max_eq_t (n) (c1) (c2): đâšn,c1 âš c2â© â rtc_eq_t c1 c2 â
      â§â§ đâšn,c1â© & đâšn,c2â©.
#n #c1 #c2 #H #Hc12
elim (rtc_ism_inv_max âŠ H) -H #n1 #n2 #Hc1 #Hc2 #H destruct
lapply (rtc_ism_eq_t_trans âŠ Hc1 âŠ Hc12) -Hc12 #H
<(rtc_ism_inj âŠ H âŠ Hc2) -Hc2
<nmax_idem /2 width=1 by conj/
qed-.
