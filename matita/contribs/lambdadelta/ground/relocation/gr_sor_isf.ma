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

include "ground/relocation/gr_isf_eq.ma".
include "ground/relocation/gr_sor_fcla.ma".

(* RELATIONAL UNION FOR GENERIC RELOCATION MAPS ***********************************************************)

(* Properties with test for finite colength *********************************)

(*** sor_isfin_ex *)
lemma gr_sor_isf_bi:
      ∀f1,f2. 𝐅❪f1❫ → 𝐅❪f2❫ → ∃∃f. f1 ⋓ f2 ≘ f & 𝐅❪f❫.
#f1 #f2 * #n1 #H1 * #n2 #H2 elim (gr_sor_fcla_bi … H1 … H2) -H1 -H2
/3 width=4 by ex2_intro, ex_intro/
qed-.

(* Forward lemmas with test for finite colength *****************************)

(*** sor_fwd_isfin_sn *)
lemma gr_sor_des_isf_sn:
      ∀f. 𝐅❪f❫ → ∀f1,f2. f1 ⋓ f2 ≘ f → 𝐅❪f1❫.
#f * #n #Hf #f1 #f2 #H
elim (gr_sor_des_fcla_sn … Hf … H) -f -f2 /2 width=2 by ex_intro/
qed-.

(*** sor_fwd_isfin_dx *)
lemma gr_sor_des_isf_dx:
      ∀f. 𝐅❪f❫ → ∀f1,f2. f1 ⋓ f2 ≘ f → 𝐅❪f2❫.
#f * #n #Hf #f1 #f2 #H
elim (gr_sor_des_fcla_dx … Hf … H) -f -f1 /2 width=2 by ex_intro/
qed-.

(* Inversion lemmas with test for finite colength ***************************)

(*** sor_isfin *)
lemma gr_sor_inv_isf_bi:
      ∀f1,f2. 𝐅❪f1❫ → 𝐅❪f2❫ → ∀f. f1 ⋓ f2 ≘ f → 𝐅❪f❫.
#f1 #f2 #Hf1 #Hf2 #f #Hf elim (gr_sor_isf_bi … Hf1 … Hf2) -Hf1 -Hf2
/3 width=6 by gr_sor_mono, gr_isf_eq_repl_back/
qed-.

(*** sor_inv_isfin3 *)
lemma gr_sor_inv_isf:
      ∀f1,f2,f. f1 ⋓ f2 ≘ f → 𝐅❪f❫ →
      ∧∧ 𝐅❪f1❫ & 𝐅❪f2❫.
/3 width=4 by gr_sor_des_isf_dx, gr_sor_des_isf_sn, conj/ qed-.
