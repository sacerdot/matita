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
include "ground/steps/rtc_plus.ma".
include "ground/steps/rtc_isrt.ma".

(* RT-TRANSITION COUNTER ****************************************************)

(* Properties with test for constrained rt-transition counter ***************)

lemma isrt_plus: ∀n1,n2,c1,c2. 𝐑𝐓❪n1,c1❫ → 𝐑𝐓❪n2,c2❫ → 𝐑𝐓❪n1+n2,c1+c2❫.
#n1 #n2 #c1 #c2 * #ri1 #rs1 #H1 * #ri2 #rs2 #H2 destruct
/2 width=3 by ex1_2_intro/
qed.

lemma isrt_plus_O1: ∀n,c1,c2. 𝐑𝐓❪0,c1❫ → 𝐑𝐓❪n,c2❫ → 𝐑𝐓❪n,c1+c2❫.
/2 width=1 by isrt_plus/ qed.

lemma isrt_plus_O2: ∀n,c1,c2. 𝐑𝐓❪n,c1❫ → 𝐑𝐓❪0,c2❫ → 𝐑𝐓❪n,c1+c2❫.
#n #c1 #c2 #H1 #H2 >(plus_n_O n) /2 width=1 by isrt_plus/
qed.

lemma isrt_succ: ∀n,c. 𝐑𝐓❪n,c❫ → 𝐑𝐓❪↑n,c+𝟘𝟙❫.
/2 width=1 by isrt_plus/ qed.

(* Inversion properties with test for constrained rt-transition counter *****)

lemma isrt_inv_plus: ∀n,c1,c2. 𝐑𝐓❪n,c1 + c2❫ →
                     ∃∃n1,n2. 𝐑𝐓❪n1,c1❫ & 𝐑𝐓❪n2,c2❫ & n1 + n2 = n.
#n #c1 #c2 * #ri #rs #H
elim (plus_inv_dx … H) -H #ri1 #rs1 #ti1 #ts1 #ri2 #rs2 #ti2 #ts2 #_ #_ #H1 #H2 #H3 #H4
elim (plus_inv_O3 … H1) -H1 /3 width=5 by ex3_2_intro, ex1_2_intro/
qed-.

lemma isrt_inv_plus_O_dx: ∀n,c1,c2. 𝐑𝐓❪n,c1 + c2❫ → 𝐑𝐓❪0,c2❫ → 𝐑𝐓❪n,c1❫.
#n #c1 #c2 #H #H2
elim (isrt_inv_plus … H) -H #n1 #n2 #Hn1 #Hn2 #H destruct
lapply (isrt_inj … Hn2 H2) -c2 #H destruct //
qed-.

lemma isrt_inv_plus_SO_dx: ∀n,c1,c2. 𝐑𝐓❪n,c1 + c2❫ → 𝐑𝐓❪1,c2❫ →
                           ∃∃m. 𝐑𝐓❪m,c1❫ & n = ↑m.
#n #c1 #c2 #H #H2
elim (isrt_inv_plus … H) -H #n1 #n2 #Hn1 #Hn2 #H destruct
lapply (isrt_inj … Hn2 H2) -c2 #H destruct
/2 width=3 by ex2_intro/
qed-.
