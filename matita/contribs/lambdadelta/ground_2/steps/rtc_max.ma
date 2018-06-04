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

include "ground_2/steps/rtc_shift.ma".

(* RT-TRANSITION COUNTER ****************************************************)

definition max (c1:rtc) (c2:rtc): rtc ≝ match c1 with [
   mk_rtc ri1 rs1 ti1 ts1 ⇒ match c2 with [
      mk_rtc ri2 rs2 ti2 ts2 ⇒ 〈ri1∨ri2, rs1∨rs2, ti1∨ti2, ts1∨ts2〉
   ]
].

interpretation "maximum (rtc)"
   'or c1 c2 = (max c1 c2).

(* Basic properties *********************************************************)

lemma max_rew: ∀ri1,ri2,rs1,rs2,ti1,ti2,ts1,ts2.
                 〈ri1∨ri2, rs1∨rs2, ti1∨ti2, ts1∨ts2〉 =
                 (〈ri1,rs1,ti1,ts1〉 ∨ 〈ri2,rs2,ti2,ts2〉).
// qed.

lemma max_O_dx: ∀c. c = (c ∨ 𝟘𝟘).
* #ri #rs #ti #ts <max_rew //
qed.

lemma max_idem: ∀c. c = (c ∨ c).
* #ri #rs #ti #ts <max_rew //
qed.

(* Basic inversion properties ***********************************************)

lemma max_inv_dx: ∀ri,rs,ti,ts,c1,c2. 〈ri,rs,ti,ts〉 = (c1 ∨ c2) →
                  ∃∃ri1,rs1,ti1,ts1,ri2,rs2,ti2,ts2.
                  (ri1∨ri2) = ri & (rs1∨rs2) = rs & (ti1∨ti2) = ti & (ts1∨ts2) = ts &
                  〈ri1,rs1,ti1,ts1〉 = c1 & 〈ri2,rs2,ti2,ts2〉 = c2.
#ri #rs #ti #ts * #ri1 #rs1 #ti1 #ts1 * #ri2 #rs2 #ti2 #ts2
<max_rew #H destruct /2 width=14 by ex6_8_intro/
qed-.

(* Main Properties **********************************************************)

theorem max_assoc: associative … max.
* #ri1 #rs1 #ti1 #ts1 * #ri2 #rs2 #ti2 #ts2 * #ri3 #rs3 #ti3 #ts3
<max_rew <max_rew //
qed.

(* Properties with test for constrained rt-transition counter ***************)

lemma isrt_max: ∀n1,n2,c1,c2. 𝐑𝐓⦃n1, c1⦄ → 𝐑𝐓⦃n2, c2⦄ → 𝐑𝐓⦃n1∨n2, c1∨c2⦄.
#n1 #n2 #c1 #c2 * #ri1 #rs1 #H1 * #ri2 #rs2 #H2 destruct
/2 width=3 by ex1_2_intro/
qed.

lemma isrt_max_O1: ∀n,c1,c2. 𝐑𝐓⦃0, c1⦄ → 𝐑𝐓⦃n, c2⦄ → 𝐑𝐓⦃n, c1∨c2⦄.
/2 width=1 by isrt_max/ qed.

lemma isrt_max_O2: ∀n,c1,c2. 𝐑𝐓⦃n, c1⦄ → 𝐑𝐓⦃0, c2⦄ → 𝐑𝐓⦃n, c1∨c2⦄.
#n #c1 #c2 #H1 #H2 >(max_O2 n) /2 width=1 by isrt_max/
qed.

lemma isrt_max_idem1: ∀n,c1,c2. 𝐑𝐓⦃n, c1⦄ → 𝐑𝐓⦃n, c2⦄ → 𝐑𝐓⦃n, c1∨c2⦄.
#n #c1 #c2 #H1 #H2 >(idempotent_max n) /2 width=1 by isrt_max/
qed.

(* Inversion properties with test for constrained rt-transition counter *****)

lemma isrt_inv_max: ∀n,c1,c2. 𝐑𝐓⦃n, c1 ∨ c2⦄ →
                    ∃∃n1,n2. 𝐑𝐓⦃n1, c1⦄ & 𝐑𝐓⦃n2, c2⦄ & (n1 ∨ n2) = n.
#n #c1 #c2 * #ri #rs #H
elim (max_inv_dx … H) -H #ri1 #rs1 #ti1 #ts1 #ri2 #rs2 #ti2 #ts2 #_ #_ #H1 #H2 #H3 #H4
elim (max_inv_O3 … H1) -H1 /3 width=5 by ex3_2_intro, ex1_2_intro/
qed-.

lemma isrt_O_inv_max: ∀c1,c2. 𝐑𝐓⦃0, c1 ∨ c2⦄ → ∧∧ 𝐑𝐓⦃0, c1⦄ & 𝐑𝐓⦃0, c2⦄.
#c1 #c2 #H
elim (isrt_inv_max … H) -H #n1 #n2 #Hn1 #Hn2 #H
elim (max_inv_O3 … H) -H #H1 #H2 destruct
/2 width=1 by conj/
qed-.

lemma isrt_inv_max_O_dx: ∀n,c1,c2. 𝐑𝐓⦃n, c1 ∨ c2⦄ → 𝐑𝐓⦃0, c2⦄ → 𝐑𝐓⦃n, c1⦄.
#n #c1 #c2 #H #H2
elim (isrt_inv_max … H) -H #n1 #n2 #Hn1 #Hn2 #H destruct
lapply (isrt_inj … Hn2 H2) -c2 #H destruct //
qed-.

lemma isrt_inv_max_eq_t: ∀n,c1,c2. 𝐑𝐓⦃n, c1 ∨ c2⦄ → eq_t c1 c2 →
                         ∧∧ 𝐑𝐓⦃n, c1⦄ & 𝐑𝐓⦃n, c2⦄.
#n #c1 #c2 #H #Hc12
elim (isrt_inv_max … H) -H #n1 #n2 #Hc1 #Hc2 #H destruct
lapply (isrt_eq_t_trans … Hc1 … Hc12) -Hc12 #H
<(isrt_inj … H … Hc2) -Hc2
<idempotent_max /2 width=1 by conj/
qed-.

(* Properties with shift ****************************************************)

lemma max_shift: ∀c1,c2. ((↕*c1) ∨ (↕*c2)) = ↕*(c1∨c2).
* #ri1 #rs1 #ti1 #ts1 * #ri2 #rs2 #ti2 #ts2
<shift_rew <shift_rew <shift_rew <max_rew //
qed.

(* Inversion lemmaswith shift ***********************************************)

lemma isrt_inv_max_shift_sn: ∀n,c1,c2. 𝐑𝐓⦃n, ↕*c1 ∨ c2⦄ →
                             ∧∧ 𝐑𝐓⦃0, c1⦄ & 𝐑𝐓⦃n, c2⦄.
#n #c1 #c2 #H
elim (isrt_inv_max … H) -H #n1 #n2 #Hc1 #Hc2 #H destruct
elim (isrt_inv_shift … Hc1) -Hc1 #Hc1 * -n1
/2 width=1 by conj/
qed-.
