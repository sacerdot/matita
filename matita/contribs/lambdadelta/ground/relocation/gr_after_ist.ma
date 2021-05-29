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

include "ground/relocation/gr_pat_lt.ma".
include "ground/relocation/gr_ist.ma".
include "ground/relocation/gr_after_pat.ma".

(* RELATIONAL COMPOSITION FOR GENERIC RELOCATION MAPS ***********************************************************)

(* Forward lemmas on istot **************************************************)

(*** after_istot_fwd *)
lemma gr_after_ist_des:
      ∀f2,f1,f. f2 ⊚ f1 ≘ f → 𝐓❪f2❫ → 𝐓❪f1❫ → 𝐓❪f❫.
#f2 #f1 #f #Hf #Hf2 #Hf1 #i1 elim (Hf1 i1) -Hf1
#i2 #Hf1 elim (Hf2 i2) -Hf2
/3 width=7 by gr_after_des_pat, ex_intro/
qed-.

(*** after_fwd_istot_dx *)
lemma gr_after_des_ist_dx:
      ∀f2,f1,f. f2 ⊚ f1 ≘ f → 𝐓❪f❫ → 𝐓❪f1❫.
#f2 #f1 #f #H #Hf #i1 elim (Hf i1) -Hf
#i2 #Hf elim (gr_after_pat_des … Hf … H) -f /2 width=2 by ex_intro/
qed-.

(*** after_fwd_istot_sn *)
lemma gr_after_des_ist_sn:
      ∀f2,f1,f. f2 ⊚ f1 ≘ f → 𝐓❪f❫ → 𝐓❪f2❫.
#f2 #f1 #f #H #Hf #i1 elim (Hf i1) -Hf
#i #Hf elim (gr_after_pat_des … Hf … H) -f
#i2 #Hf1 #Hf2 lapply (gr_pat_increasing … Hf1) -f1
#Hi12 elim (gr_pat_le_ex … Hf2 … Hi12) -i2 /2 width=2 by ex_intro/
qed-.

(*** after_at1_fwd *)
lemma gr_after_des_ist_pat:
      ∀f1,i1,i2. @❪i1, f1❫ ≘ i2 → ∀f2. 𝐓❪f2❫ → ∀f. f2 ⊚ f1 ≘ f →
      ∃∃i. @❪i2, f2❫ ≘ i & @❪i1, f❫ ≘ i.
#f1 #i1 #i2 #Hf1 #f2 #Hf2 #f #Hf elim (Hf2 i2) -Hf2
/3 width=8 by gr_after_des_pat, ex2_intro/
qed-.

(* Inversions with gr_ist *)

(*** after_inv_istot *)
lemma gr_after_inv_ist:
      ∀f2,f1,f. f2 ⊚ f1 ≘ f → 𝐓❪f❫ → ∧∧ 𝐓❪f2❫ & 𝐓❪f1❫.
/3 width=4 by gr_after_des_ist_sn, gr_after_des_ist_dx, conj/ qed-.
