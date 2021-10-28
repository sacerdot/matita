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

include "ground/relocation/pr_pat_lt.ma".
include "ground/relocation/pr_nat.ma".
include "ground/relocation/pr_ist.ma".
include "ground/relocation/pr_after_pat.ma".

(* RELATIONAL COMPOSITION FOR PARTIAL RELOCATION MAPS ***********************)

(* Destructions with pr_ist *************************************************)

(*** after_istot_fwd *)
lemma pr_after_ist_des:
      ∀f2,f1,f. f2 ⊚ f1 ≘ f → 𝐓❪f2❫ → 𝐓❪f1❫ → 𝐓❪f❫.
#f2 #f1 #f #Hf #Hf2 #Hf1 #i1 elim (Hf1 i1) -Hf1
#i2 #Hf1 elim (Hf2 i2) -Hf2
/3 width=7 by pr_after_des_pat, ex_intro/
qed-.

(*** after_fwd_istot_dx *)
lemma pr_after_des_ist_dx:
      ∀f2,f1,f. f2 ⊚ f1 ≘ f → 𝐓❪f❫ → 𝐓❪f1❫.
#f2 #f1 #f #H #Hf #i1 elim (Hf i1) -Hf
#i2 #Hf elim (pr_after_pat_des … Hf … H) -f /2 width=2 by ex_intro/
qed-.

(*** after_fwd_istot_sn *)
lemma pr_after_des_ist_sn:
      ∀f2,f1,f. f2 ⊚ f1 ≘ f → 𝐓❪f❫ → 𝐓❪f2❫.
#f2 #f1 #f #H #Hf #i1 elim (Hf i1) -Hf
#i #Hf elim (pr_after_pat_des … Hf … H) -f
#i2 #Hf1 #Hf2 lapply (pr_pat_increasing … Hf1) -f1
#Hi12 elim (pr_pat_le_ex … Hf2 … Hi12) -i2 /2 width=2 by ex_intro/
qed-.

(*** after_at1_fwd *)
lemma pr_after_des_ist_pat:
      ∀f1,i1,i2. @❪i1, f1❫ ≘ i2 → ∀f2. 𝐓❪f2❫ → ∀f. f2 ⊚ f1 ≘ f →
      ∃∃i. @❪i2, f2❫ ≘ i & @❪i1, f❫ ≘ i.
#f1 #i1 #i2 #Hf1 #f2 #Hf2 #f #Hf elim (Hf2 i2) -Hf2
/3 width=8 by pr_after_des_pat, ex2_intro/
qed-.

lemma pr_after_des_ist_nat:
      ∀f1,l1,l2. @↑❪l1, f1❫ ≘ l2 → ∀f2. 𝐓❪f2❫ → ∀f. f2 ⊚ f1 ≘ f →
      ∃∃l. @↑❪l2, f2❫ ≘ l & @↑❪l1, f❫ ≘ l.
#f1 #l1 #l2 #H1 #f2 #H2 #f #Hf
elim (pr_after_des_ist_pat … H1 … H2 … Hf) -f1 -H2
/2 width=3 by ex2_intro/
qed-.

(* Inversions with pr_ist ***************************************************)

(*** after_inv_istot *)
lemma pr_after_inv_ist:
      ∀f2,f1,f. f2 ⊚ f1 ≘ f → 𝐓❪f❫ → ∧∧ 𝐓❪f2❫ & 𝐓❪f1❫.
/3 width=4 by pr_after_des_ist_sn, pr_after_des_ist_dx, conj/ qed-.
