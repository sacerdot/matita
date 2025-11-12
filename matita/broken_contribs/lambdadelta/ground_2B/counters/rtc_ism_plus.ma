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
include "ground_2B/counters/rtc_plus.ma".
include "ground_2B/counters/rtc_ism.ma".

(* T-BOUND RT-TRANSITION COUNTERS *******************************************)

(* Constructions with rtc_plus **********************************************)

lemma rtc_ism_plus (n1) (n2) (c1) (c2):  𝐌❨n1,c1❩ → 𝐌❨n2,c2❩ → 𝐌❨n1+n2,c1+c2❩.
#n1 #n2 #c1 #c2 * #ri1 #rs1 #H1 * #ri2 #rs2 #H2 destruct
/2 width=3 by ex1_2_intro/
qed.

lemma rtc_ism_plus_zero_sn (n) (c1) (c2): 𝐌❨𝟎,c1❩ → 𝐌❨n,c2❩ → 𝐌❨n,c1+c2❩.
#n #c1 #c2 #H1 #H2 >(nplus_zero_sx n) /2 width=1 by rtc_ism_plus/
qed.

lemma rtc_ism_plus_zero_dx (n) (c1) (c2): 𝐌❨n,c1❩ → 𝐌❨𝟎,c2❩ → 𝐌❨n,c1+c2❩.
/2 width=1 by rtc_ism_plus/ qed.

lemma rtc_ism_succ (n) (c): 𝐌❨n,c❩ → 𝐌❨⁤↑n,c+𝟘𝟙❩.
#n #c #H >nplus_unit_dx
/2 width=1 by rtc_ism_plus/
qed.

(* Inversions with rtc_plus *************************************************)

lemma rtc_ism_inv_plus (n) (c1) (c2): 𝐌❨n,c1 + c2❩ →
      ∃∃n1,n2. 𝐌❨n1,c1❩ & 𝐌❨n2,c2❩ & n1 + n2 = n.
#n #c1 #c2 * #ri #rs #H
elim (rtc_plus_inv_dx … H) -H #ri1 #rs1 #ti1 #ts1 #ri2 #rs2 #ti2 #ts2 #_ #_ #H1 #H2 #H3 #H4
elim (eq_inv_nplus_zero … H1) -H1 /3 width=5 by ex3_2_intro, ex1_2_intro/
qed-.

lemma rtc_ism_inv_plus_zero_dx (n) (c1) (c2): 𝐌❨n,c1 + c2❩ → 𝐌❨𝟎,c2❩ → 𝐌❨n,c1❩.
#n #c1 #c2 #H #H2
elim (rtc_ism_inv_plus … H) -H #n1 #n2 #Hn1 #Hn2 #H destruct
lapply (rtc_ism_inj … Hn2 H2) -c2 #H destruct //
qed-.

lemma rtc_ism_inv_plus_unit_dx (n) (c1) (c2): 𝐌❨n,c1 + c2❩ → 𝐌❨⁤𝟏,c2❩ →
      ∃∃m. 𝐌❨m,c1❩ & n = (⁤↑m).
#n #c1 #c2 #H #H2
elim (rtc_ism_inv_plus … H) -H #n1 #n2 #Hn1 #Hn2 #H destruct
lapply (rtc_ism_inj … Hn2 H2) -c2 #H destruct
/2 width=3 by ex2_intro/
qed-.
