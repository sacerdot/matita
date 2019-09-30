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

include "ground_2/steps/rtc_max.ma".
include "ground_2/steps/rtc_ist.ma".

(* RT-TRANSITION COUNTER ****************************************************)

(* Properties with test for t-transition counter ****************************)

lemma ist_max: ∀n1,n2,c1,c2. 𝐓⦃n1,c1⦄ → 𝐓⦃n2,c2⦄ → 𝐓⦃n1∨n2,c1∨c2⦄.
#n1 #n2 #c1 #c2 #H1 #H2 destruct //
qed.

lemma ist_max_O1: ∀n,c1,c2. 𝐓⦃0,c1⦄ → 𝐓⦃n,c2⦄ → 𝐓⦃n,c1∨c2⦄.
/2 width=1 by ist_max/ qed.

lemma ist_max_O2: ∀n,c1,c2. 𝐓⦃n,c1⦄ → 𝐓⦃0,c2⦄ → 𝐓⦃n,c1∨c2⦄.
#n #c1 #c2 #H1 #H2 >(max_O2 n) /2 width=1 by ist_max/
qed.

lemma ist_max_idem1: ∀n,c1,c2. 𝐓⦃n,c1⦄ → 𝐓⦃n,c2⦄ → 𝐓⦃n,c1∨c2⦄.
#n #c1 #c2 #H1 #H2 >(idempotent_max n) /2 width=1 by ist_max/
qed.

(* Inversion properties with test for t-transition counter ******************)

lemma ist_inv_max:
      ∀n,c1,c2. 𝐓⦃n,c1 ∨ c2⦄ →
      ∃∃n1,n2. 𝐓⦃n1,c1⦄ & 𝐓⦃n2,c2⦄ & (n1 ∨ n2) = n.
#n #c1 #c2 #H
elim (max_inv_dx … H) -H #ri1 #rs1 #ti1 #ts1 #ri2 #rs2 #ti2 #ts2 #H1 #H2 #H3 #H4 #H5 #H6 destruct
elim (max_inv_O3 … H1) -H1 #H11 #H12 destruct
elim (max_inv_O3 … H2) -H2 #H21 #H22 destruct
elim (max_inv_O3 … H3) -H3 #H31 #H32 destruct
/2 width=5 by ex3_2_intro/
qed-.

lemma ist_O_inv_max: ∀c1,c2. 𝐓⦃0,c1 ∨ c2⦄ → ∧∧ 𝐓⦃0,c1⦄ & 𝐓⦃0,c2⦄.
#c1 #c2 #H
elim (ist_inv_max … H) -H #n1 #n2 #Hn1 #Hn2 #H
elim (max_inv_O3 … H) -H #H1 #H2 destruct
/2 width=1 by conj/
qed-.

lemma ist_inv_max_O_dx: ∀n,c1,c2. 𝐓⦃n,c1 ∨ c2⦄ → 𝐓⦃0,c2⦄ → 𝐓⦃n,c1⦄.
#n #c1 #c2 #H #H2
elim (ist_inv_max … H) -H #n1 #n2 #Hn1 #Hn2 #H destruct //
qed-.
