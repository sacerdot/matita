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

include "basic_2/static/frees_frees.ma".
include "basic_2/static/fle_fqup.ma".

(* FREE VARIABLES INCLUSION FOR RESTRICTED CLOSURES *************************)

(* Advanced inversion lemmas ************************************************)

lemma fle_inv_voids_sn_frees_dx: ∀L1,L2,T1,T2,n. ⦃ⓧ*[n]L1, T1⦄ ⊆ ⦃L2, T2⦄ →
                                 |L1| = |L2| → ∀f2. L2 ⊢ 𝐅*⦃T2⦄ ≡ f2 →
                                 ∃∃f1. ⓧ*[n]L1 ⊢ 𝐅*⦃T1⦄ ≡ f1 & ⫱*[n]f1 ⊆ f2.
#L1 #L2 #T1 #T2 #n #H #HL12 #f2 #Hf2
elim (fle_inv_voids_sn … H HL12) -H -HL12 #f1 #g2 #Hf1 #Hg2 #Hfg
lapply (frees_mono … Hg2 … Hf2) -Hg2 -Hf2 #Hfg2
lapply (sle_eq_repl_back2 … Hfg … Hfg2) -g2
/2 width=3 by ex2_intro/
qed-.

(* Main properties **********************************************************)
(*
theorem fle_trans: bi_transitive … fle.
#L1 #L #T1 #T * #f1 #f #HT1 #HT #Hf1 #L2 #T2 * #g #f2 #Hg #HT2 #Hf2
/5 width=8 by frees_mono, sle_trans, sle_eq_repl_back2, ex3_2_intro/
qed-.
*)
theorem fle_bind_sn: ∀L1,L2,V1,T1,T. ⦃L1, V1⦄ ⊆ ⦃L2, T⦄ → ⦃L1.ⓧ, T1⦄ ⊆ ⦃L2, T⦄ →
                     ∀p,I. ⦃L1, ⓑ{p,I}V1.T1⦄ ⊆ ⦃L2, T⦄.
#L1 #L2 #V1 #T1 #T * -L1 #f1 #x #L1 #n1 #Hf1 #Hx #HL12 #Hf1x
>voids_succ #H #p #I
elim (fle_inv_voids_sn_frees_dx … H … Hx) -H // #f2 #Hf2
<tls_xn #Hf2x
elim (sor_isfin_ex f1 (⫱f2)) /3 width=3 by frees_fwd_isfin, isfin_tl/ #f #Hf #_
/4 width=9 by fle_intro, frees_bind_void, sor_inv_sle, sor_tls/
qed.

theorem fle_flat_sn: ∀L1,L2,V1,T1,T. ⦃L1, V1⦄ ⊆ ⦃L2, T⦄ → ⦃L1, T1⦄ ⊆ ⦃L2, T⦄ →
                     ∀I. ⦃L1, ⓕ{I}V1.T1⦄ ⊆ ⦃L2, T⦄.
#L1 #L2 #V1 #T1 #T * -L1 #f1 #x #L1 #n1 #Hf1 #Hx #HL12 #Hf1x #H #I
elim (fle_inv_voids_sn_frees_dx … H … Hx) -H // #f2 #Hf2 #Hf2x
elim (sor_isfin_ex f1 f2) /2 width=3 by frees_fwd_isfin/ #f #Hf #_
/4 width=9 by fle_intro, frees_flat, sor_inv_sle, sor_tls/
qed.
(*
lemma fle_bind: ∀L1,L2,V1,V2. ⦃L1, V1⦄ ⊆ ⦃L2, V2⦄ →
                ∀I1,I2,T1,T2. ⦃L1.ⓑ{I1}V1, T1⦄ ⊆ ⦃L2.ⓑ{I2}V2, T2⦄ →
                ∀p. ⦃L1, ⓑ{p,I1}V1.T1⦄ ⊆ ⦃L2, ⓑ{p,I2}V2.T2⦄.
#L1 #L2 #V1 #V2 * #f1 #g1 #HV1 #HV2 #Hfg1 #I1 #I2 #T1 #T2 * #f2 #g2 #Hf2 #Hg2 #Hfg2 #p
elim (sor_isfin_ex f1 (⫱f2)) /3 width=3 by frees_fwd_isfin, isfin_tl/ #f #Hf #_
elim (sor_isfin_ex g1 (⫱g2)) /3 width=3 by frees_fwd_isfin, isfin_tl/ #g #Hg #_
/4 width=12 by frees_bind, monotonic_sle_sor, sle_tl, ex3_2_intro/
qed.

lemma fle_flat: ∀L1,L2,V1,V2. ⦃L1, V1⦄ ⊆ ⦃L2, V2⦄ →
                ∀T1,T2. ⦃L1, T1⦄ ⊆ ⦃L2, T2⦄ →
                ∀I1,I2. ⦃L1, ⓕ{I1}V1.T1⦄ ⊆ ⦃L2, ⓕ{I2}V2.T2⦄.
#L1 #L2 #V1 #V2 * #f1 #g1 #HV1 #HV2 #Hfg1 #T1 #T2 * #f2 #g2 #Hf2 #Hg2 #Hfg2 #I1 #I2
elim (sor_isfin_ex f1 f2) /2 width=3 by frees_fwd_isfin/ #f #Hf #_
elim (sor_isfin_ex g1 g2) /2 width=3 by frees_fwd_isfin/ #g #Hg #_
/3 width=12 by frees_flat, monotonic_sle_sor, ex3_2_intro/
qed.
*)
