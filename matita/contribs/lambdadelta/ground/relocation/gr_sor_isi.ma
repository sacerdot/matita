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

include "ground/relocation/gr_isi_eq.ma".
include "ground/relocation/gr_sor_eq.ma".
include "ground/relocation/gr_sor_sor.ma".

(* RELATIONAL UNION FOR GENERIC RELOCATION MAPS *****************************)

(* Constructions with gr_isi ************************************************)

(*** sor_isid_sn *)
corec lemma gr_sor_isi_sn:
            ∀f1. 𝐈❪f1❫ → ∀f2. f1 ⋓ f2 ≘ f2.
#f1 * -f1
#f1 #g1 #Hf1 #H1 #f2 cases (gr_map_split_tl f2)
/3 width=7 by gr_sor_push_bi, gr_sor_push_next/
qed.

(*** sor_isid_dx *)
corec lemma gr_sor_isi_dx:
            ∀f2. 𝐈❪f2❫ → ∀f1. f1 ⋓ f2 ≘ f1.
#f2 * -f2
#f2 #g2 #Hf2 #H2 #f1 cases (gr_map_split_tl f1)
/3 width=7 by gr_sor_push_bi, gr_sor_next_push/
qed.

(*** sor_isid *)
lemma gr_sor_isi_bi_isi:
      ∀f1,f2,f. 𝐈❪f1❫ → 𝐈❪f2❫ → 𝐈❪f❫ → f1 ⋓ f2 ≘ f.
/4 width=3 by gr_sor_eq_repl_back_dx, gr_sor_eq_repl_back_sn, gr_isi_inv_eq_repl/ qed.


(* Destructions with gr_isi *************************************************)

(*** sor_fwd_isid1 *)
corec lemma gr_sor_des_isi_sn:
            ∀f1,f2,f. f1 ⋓ f2 ≘ f → 𝐈❪f❫ → 𝐈❪f1❫.
#f1 #f2 #f * -f1 -f2 -f
#f1 #f2 #f #g1 #g2 #g #Hf #H1 #H2 #H #Hg
[ /4 width=6 by gr_isi_inv_push, gr_isi_push/ ]
cases (gr_isi_inv_next … Hg … H)
qed-.

(*** sor_fwd_isid2 *)
corec lemma gr_sor_des_isi_dx:
            ∀f1,f2,f. f1 ⋓ f2 ≘ f → 𝐈❪f❫ → 𝐈❪f2❫.
#f1 #f2 #f * -f1 -f2 -f
#f1 #f2 #f #g1 #g2 #g #Hf #H1 #H2 #H #Hg
[ /4 width=6 by gr_isi_inv_push, gr_isi_push/ ]
cases (gr_isi_inv_next … Hg … H)
qed-.

(* Inversions with gr_isi ***************************************************)

(*** sor_isid_inv_sn *)
lemma gr_sor_inv_isi_sn:
      ∀f1,f2,f. f1 ⋓ f2 ≘ f → 𝐈❪f1❫ → f2 ≡ f.
/3 width=4 by gr_sor_isi_sn, gr_sor_mono/
qed-.

(*** sor_isid_inv_dx *)
lemma gr_sor_inv_isi_dx:
      ∀f1,f2,f. f1 ⋓ f2 ≘ f → 𝐈❪f2❫ → f1 ≡ f.
/3 width=4 by gr_sor_isi_dx, gr_sor_mono/
qed-.

(*** sor_inv_isid3 *)
lemma gr_sor_inv_isi:
      ∀f1,f2,f. f1 ⋓ f2 ≘ f → 𝐈❪f❫ →
      ∧∧ 𝐈❪f1❫ & 𝐈❪f2❫.
/3 width=4 by gr_sor_des_isi_dx, gr_sor_des_isi_sn, conj/ qed-.
