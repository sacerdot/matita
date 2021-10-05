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

include "static_2/syntax/lveq_lveq.ma".
include "static_2/static/fsle_fqup.ma".

(* FREE VARIABLES INCLUSION FOR RESTRICTED CLOSURES *************************)

(* Advanced inversion lemmas ************************************************)

lemma fsle_frees_trans:
      ∀L1,L2,T1,T2. ❪L1,T1❫ ⊆ ❪L2,T2❫ →
      ∀f2. L2 ⊢ 𝐅+❪T2❫ ≘ f2 →
      ∃∃n1,n2,f1. L1 ⊢ 𝐅+❪T1❫ ≘ f1 & L1 ≋ⓧ*[n1,n2] L2 & ⫰*[n1]f1 ⊆ ⫰*[n2]f2.
#L1 #L2 #T1 #T2 * #n1 #n2 #f1 #g2 #Hf1 #Hg2 #HL #Hn #f2 #Hf2
lapply (frees_mono … Hg2 … Hf2) -Hg2 -Hf2 #Hgf2
lapply (pr_tls_eq_repl n2 … Hgf2) -Hgf2 #Hgf2
lapply (pr_sle_eq_repl_back_dx … Hn … Hgf2) -g2
/2 width=6 by ex3_3_intro/
qed-.

lemma fsle_frees_trans_eq:
      ∀L1,L2. |L1| = |L2| →
      ∀T1,T2. ❪L1,T1❫ ⊆ ❪L2,T2❫ → ∀f2. L2 ⊢ 𝐅+❪T2❫ ≘ f2 →
      ∃∃f1. L1 ⊢ 𝐅+❪T1❫ ≘ f1 & f1 ⊆ f2.
#L1 #L2 #H1L #T1 #T2 #H2L #f2 #Hf2
elim (fsle_frees_trans … H2L … Hf2) -T2 #n1 #n2 #f1 #Hf1 #H2L #Hf12
elim (lveq_inj_length … H2L) // -L2 #H1 #H2 destruct
/2 width=3 by ex2_intro/
qed-.

lemma fsle_inv_frees_eq:
      ∀L1,L2. |L1| = |L2| →
      ∀T1,T2. ❪L1,T1❫ ⊆ ❪L2,T2❫ →
      ∀f1. L1 ⊢ 𝐅+❪T1❫ ≘ f1 → ∀f2. L2 ⊢ 𝐅+❪T2❫ ≘ f2 →
      f1 ⊆ f2.
#L1 #L2 #H1L #T1 #T2 #H2L #f1 #Hf1 #f2 #Hf2
elim (fsle_frees_trans_eq … H2L … Hf2) // -L2 -T2
/3 width=6 by frees_mono, pr_sle_eq_repl_back_sn/
qed-.

lemma fsle_frees_conf:
      ∀L1,L2,T1,T2. ❪L1,T1❫ ⊆ ❪L2,T2❫ →
      ∀f1. L1 ⊢ 𝐅+❪T1❫ ≘ f1 →
      ∃∃n1,n2,f2. L2 ⊢ 𝐅+❪T2❫ ≘ f2 & L1 ≋ⓧ*[n1,n2] L2 & ⫰*[n1]f1 ⊆ ⫰*[n2]f2.
#L1 #L2 #T1 #T2 * #n1 #n2 #g1 #g2 #Hg1 #Hg2 #HL #Hn #f1 #Hf1
lapply (frees_mono … Hg1 … Hf1) -Hg1 -Hf1 #Hgf1
lapply (pr_tls_eq_repl n1 … Hgf1) -Hgf1 #Hgf1
lapply (pr_sle_eq_repl_back_sn … Hn … Hgf1) -g1
/2 width=6 by ex3_3_intro/
qed-.

lemma fsle_frees_conf_eq:
      ∀L1,L2. |L1| = |L2| →
      ∀T1,T2. ❪L1,T1❫ ⊆ ❪L2,T2❫ → ∀f1. L1 ⊢ 𝐅+❪T1❫ ≘ f1 →
      ∃∃f2. L2 ⊢ 𝐅+❪T2❫ ≘ f2 & f1 ⊆ f2.
#L1 #L2 #H1L #T1 #T2 #H2L #f1 #Hf1
elim (fsle_frees_conf … H2L … Hf1) -T1 #n1 #n2 #f2 #Hf2 #H2L #Hf12
elim (lveq_inj_length … H2L) // -L1 #H1 #H2 destruct
/2 width=3 by ex2_intro/
qed-.

(* Main properties **********************************************************)

theorem fsle_trans_sn:
        ∀L1,L2,T1,T. ❪L1,T1❫ ⊆ ❪L2,T❫ →
        ∀T2. ❪L2,T❫ ⊆ ❪L2,T2❫ → ❪L1,T1❫ ⊆ ❪L2,T2❫.
#L1 #L2 #T1 #T
* #m1 #m0 #g1 #g0 #Hg1 #Hg0 #Hm #Hg
#T2
* #n0 #n2 #f0 #f2 #Hf0 #Hf2 #Hn #Hf
lapply (frees_mono … Hf0 … Hg0) -Hf0 -Hg0 #Hfg0
elim (lveq_inj_length … Hn) // -Hn #H1 #H2 destruct
lapply (pr_sle_eq_repl_back_sn … Hf … Hfg0) -f0
/4 width=10 by pr_sle_tls, pr_sle_trans, ex4_4_intro/
qed-.

theorem fsle_trans_dx:
        ∀L1,T1,T. ❪L1,T1❫ ⊆ ❪L1,T❫ →
        ∀L2,T2. ❪L1,T❫ ⊆ ❪L2,T2❫ → ❪L1,T1❫ ⊆ ❪L2,T2❫.
#L1 #T1 #T
* #m1 #m0 #g1 #g0 #Hg1 #Hg0 #Hm #Hg
#L2 #T2
* #n0 #n2 #f0 #f2 #Hf0 #Hf2 #Hn #Hf
lapply (frees_mono … Hg0 … Hf0) -Hg0 -Hf0 #Hgf0
elim (lveq_inj_length … Hm) // -Hm #H1 #H2 destruct
lapply (pr_sle_eq_repl_back_dx … Hg … Hgf0) -g0
/4 width=10 by pr_sle_tls, pr_sle_trans, ex4_4_intro/
qed-.

theorem fsle_trans_rc:
        ∀L1,L,T1,T. |L1| = |L| → ❪L1,T1❫ ⊆ ❪L,T❫ →
        ∀L2,T2. |L| = |L2| → ❪L,T❫ ⊆ ❪L2,T2❫ → ❪L1,T1❫ ⊆ ❪L2,T2❫.
#L1 #L #T1 #T #HL1
* #m1 #m0 #g1 #g0 #Hg1 #Hg0 #Hm #Hg
#L2 #T2 #HL2
* #n0 #n2 #f0 #f2 #Hf0 #Hf2 #Hn #Hf
lapply (frees_mono … Hg0 … Hf0) -Hg0 -Hf0 #Hgf0
elim (lveq_inj_length … Hm) // -Hm #H1 #H2 destruct
elim (lveq_inj_length … Hn) // -Hn #H1 #H2 destruct
lapply (pr_sle_eq_repl_back_dx … Hg … Hgf0) -g0
/3 width=10 by lveq_length_eq, pr_sle_trans, ex4_4_intro/
qed-.

theorem fsle_bind_sn_ge:
        ∀L1,L2. |L2| ≤ |L1| →
        ∀V1,T1,T. ❪L1,V1❫ ⊆ ❪L2,T❫ → ❪L1.ⓧ,T1❫ ⊆ ❪L2,T❫ →
        ∀p,I. ❪L1,ⓑ[p,I]V1.T1❫ ⊆ ❪L2,T❫.
#L1 #L2 #HL #V1 #T1 #T * #n1 #x #f1 #g #Hf1 #Hg #H1n1 #H2n1 #H #p #I
elim (fsle_frees_trans … H … Hg) -H #n2 #n #f2 #Hf2 #H1n2 #H2n2
elim (lveq_inj_void_sn_ge … H1n1 … H1n2) -H1n2 // #H1 #H2 #H3 destruct
elim (pr_sor_isf_bi f1 (⫰f2)) /3 width=3 by frees_fwd_isfin, pr_isf_tl/ #f #Hf #_
<pr_tls_swap in H2n2; #H2n2
/4 width=12 by frees_bind_void, pr_sor_inv_sle_bi, pr_sor_tls, ex4_4_intro/
qed.

theorem fsle_flat_sn:
        ∀L1,L2,V1,T1,T. ❪L1,V1❫ ⊆ ❪L2,T❫ → ❪L1,T1❫ ⊆ ❪L2,T❫ →
        ∀I. ❪L1,ⓕ[I]V1.T1❫ ⊆ ❪L2,T❫.
#L1 #L2 #V1 #T1 #T * #n1 #x #f1 #g #Hf1 #Hg #H1n1 #H2n1 #H #I
elim (fsle_frees_trans … H … Hg) -H #n2 #n #f2 #Hf2 #H1n2 #H2n2
elim (lveq_inj … H1n1 … H1n2) -H1n2 #H1 #H2 destruct
elim (pr_sor_isf_bi f1 f2) /2 width=3 by frees_fwd_isfin/ #f #Hf #_
/4 width=12 by frees_flat, pr_sor_inv_sle_bi, pr_sor_tls, ex4_4_intro/
qed.

theorem fsle_bind_eq:
        ∀L1,L2. |L1| = |L2| → ∀V1,V2. ❪L1,V1❫ ⊆ ❪L2,V2❫ →
        ∀I2,T1,T2. ❪L1.ⓧ,T1❫ ⊆ ❪L2.ⓑ[I2]V2,T2❫ →
        ∀p,I1. ❪L1,ⓑ[p,I1]V1.T1❫ ⊆ ❪L2,ⓑ[p,I2]V2.T2❫.
#L1 #L2 #HL #V1 #V2
* #n1 #m1 #f1 #g1 #Hf1 #Hg1 #H1L #Hfg1 #I2 #T1 #T2
* #n2 #m2 #f2 #g2 #Hf2 #Hg2 #H2L #Hfg2 #p #I1
elim (lveq_inj_length … H1L) // #H1 #H2 destruct
elim (lveq_inj_length … H2L) // -HL -H2L #H1 #H2 destruct
elim (pr_sor_isf_bi f1 (⫰f2)) /3 width=3 by frees_fwd_isfin, pr_isf_tl/ #f #Hf #_
elim (pr_sor_isf_bi g1 (⫰g2)) /3 width=3 by frees_fwd_isfin, pr_isf_tl/ #g #Hg #_
/4 width=15 by frees_bind_void, frees_bind, pr_sor_monotonic_sle, pr_sle_tl, ex4_4_intro/
qed.

theorem fsle_bind:
        ∀L1,L2,V1,V2. ❪L1,V1❫ ⊆ ❪L2,V2❫ →
        ∀I1,I2,T1,T2. ❪L1.ⓑ[I1]V1,T1❫ ⊆ ❪L2.ⓑ[I2]V2,T2❫ →
        ∀p. ❪L1,ⓑ[p,I1]V1.T1❫ ⊆ ❪L2,ⓑ[p,I2]V2.T2❫.
#L1 #L2 #V1 #V2
* #n1 #m1 #f1 #g1 #Hf1 #Hg1 #H1L #Hfg1 #I1 #I2 #T1 #T2
* #n2 #m2 #f2 #g2 #Hf2 #Hg2 #H2L #Hfg2 #p
elim (lveq_inv_pair_pair … H2L) -H2L #H2L #H1 #H2 destruct
elim (lveq_inj … H2L … H1L) -H1L #H1 #H2 destruct
elim (pr_sor_isf_bi f1 (⫰f2)) /3 width=3 by frees_fwd_isfin, pr_isf_tl/ #f #Hf #_
elim (pr_sor_isf_bi g1 (⫰g2)) /3 width=3 by frees_fwd_isfin, pr_isf_tl/ #g #Hg #_
/4 width=15 by frees_bind, pr_sor_monotonic_sle, pr_sle_tl, ex4_4_intro/
qed.

theorem fsle_flat:
        ∀L1,L2,V1,V2. ❪L1,V1❫ ⊆ ❪L2,V2❫ →
        ∀T1,T2. ❪L1,T1❫ ⊆ ❪L2,T2❫ →
        ∀I1,I2. ❪L1,ⓕ[I1]V1.T1❫ ⊆ ❪L2,ⓕ[I2]V2.T2❫.
/3 width=1 by fsle_flat_sn, fsle_flat_dx_dx, fsle_flat_dx_sn/ qed-.
