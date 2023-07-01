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

include "ground/relocation/p1/pr_isf_eq.ma".
include "ground/relocation/p1/pr_sor_fcla.ma".

(* RELATIONAL UNION FOR PARTIAL RELOCATION MAPS *****************************)

(* Constructions with pr_isf ************************************************)

(*** sor_isfin_ex *)
lemma pr_sor_isf_bi:
      ∀f1,f2. 𝐅❨f1❩ → 𝐅❨f2❩ → ∃∃f. f1 ⋓ f2 ≘ f & 𝐅❨f❩.
#f1 #f2 * #n1 #H1 * #n2 #H2 elim (pr_sor_fcla_bi … H1 … H2) -H1 -H2
/3 width=4 by ex2_intro, ex_intro/
qed-.

(* Destructions with pr_isf *************************************************)

(*** sor_fwd_isfin_sn *)
lemma pr_sor_des_isf_sn:
      ∀f. 𝐅❨f❩ → ∀f1,f2. f1 ⋓ f2 ≘ f → 𝐅❨f1❩.
#f * #n #Hf #f1 #f2 #H
elim (pr_sor_des_fcla_sn … Hf … H) -f -f2 /2 width=2 by ex_intro/
qed-.

(*** sor_fwd_isfin_dx *)
lemma pr_sor_des_isf_dx:
      ∀f. 𝐅❨f❩ → ∀f1,f2. f1 ⋓ f2 ≘ f → 𝐅❨f2❩.
#f * #n #Hf #f1 #f2 #H
elim (pr_sor_des_fcla_dx … Hf … H) -f -f1 /2 width=2 by ex_intro/
qed-.

(* Inversions with pr_isf ***************************************************)

(*** sor_isfin *)
lemma pr_sor_inv_isf_bi:
      ∀f1,f2. 𝐅❨f1❩ → 𝐅❨f2❩ → ∀f. f1 ⋓ f2 ≘ f → 𝐅❨f❩.
#f1 #f2 #Hf1 #Hf2 #f #Hf elim (pr_sor_isf_bi … Hf1 … Hf2) -Hf1 -Hf2
/3 width=6 by pr_sor_mono, pr_isf_eq_repl_back/
qed-.

(*** sor_inv_isfin3 *)
lemma pr_sor_inv_isf:
      ∀f1,f2,f. f1 ⋓ f2 ≘ f → 𝐅❨f❩ →
      ∧∧ 𝐅❨f1❩ & 𝐅❨f2❩.
/3 width=4 by pr_sor_des_isf_dx, pr_sor_des_isf_sn, conj/ qed-.
