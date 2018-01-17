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

include "basic_2/syntax/lveq_length.ma".
include "basic_2/static/frees_fqup.ma".
include "basic_2/static/fle.ma".

(* FREE VARIABLES INCLUSION FOR RESTRICTED CLOSURES *************************)

(* Advanced properties ******************************************************)

lemma fle_refl: bi_reflexive … fle.
#L #T
elim (frees_total L T) #f #Hf
/2 width=8 by sle_refl, ex4_4_intro/
qed.

lemma fle_bind_dx_sn: ∀L1,L2,V1,V2. ⦃L1, V1⦄ ⊆ ⦃L2, V2⦄ →
                      ∀p,I,T2. ⦃L1, V1⦄ ⊆ ⦃L2, ⓑ{p,I}V2.T2⦄.
#L1 #L2 #V1 #V2 * #n1 #m1 #f1 #g1 #Hf1 #Hg1 #HL12 #Hfg1 #p #I #T2
elim (frees_total (L2.ⓧ) T2) #g2 #Hg2
elim (sor_isfin_ex g1 (⫱g2)) /3 width=3 by frees_fwd_isfin, isfin_tl/ #g #Hg #_
@(ex4_4_intro … g Hf1 … HL12) (**) (* full auto too slow *)
/4 width=5 by frees_bind_void, sor_inv_sle_sn, sor_tls, sle_trans/
qed.

lemma fle_bind_dx_dx: ∀L1,L2,T1,T2. ⦃L1, T1⦄ ⊆ ⦃L2.ⓧ, T2⦄ → |L1| ≤ |L2| →
                      ∀p,I,V2. ⦃L1, T1⦄ ⊆ ⦃L2, ⓑ{p,I}V2.T2⦄.
#L1 #L2 #T1 #T2 * #n1 #x1 #f2 #g2 #Hf2 #Hg2 #H #Hfg2 #HL12 #p #I #V2
elim (lveq_inv_void_dx_length … H HL12) -H -HL12 #m1 #HL12 #H1 #H2 destruct
<tls_xn in Hfg2; #Hfg2
elim (frees_total L2 V2) #g1 #Hg1
elim (sor_isfin_ex g1 (⫱g2)) /3 width=3 by frees_fwd_isfin, isfin_tl/ #g #Hg #_
@(ex4_4_intro … g Hf2 … HL12) (**) (* full auto too slow *)
/4 width=5 by frees_bind_void, sor_inv_sle_dx, sor_tls, sle_trans/
qed.

lemma fle_flat_dx_sn: ∀L1,L2,V1,V2. ⦃L1, V1⦄ ⊆ ⦃L2, V2⦄ →
                      ∀I,T2. ⦃L1, V1⦄ ⊆ ⦃L2, ⓕ{I}V2.T2⦄.
#L1 #L2 #V1 #V2 * #n1 #m1 #f1 #g1 #Hf1 #Hg1 #HL12 #Hfg1 #I #T2
elim (frees_total L2 T2) #g2 #Hg2
elim (sor_isfin_ex g1 g2) /2 width=3 by frees_fwd_isfin/ #g #Hg #_
@(ex4_4_intro … g Hf1 … HL12) (**) (* full auto too slow *)
/4 width=5 by frees_flat, sor_inv_sle_sn, sor_tls, sle_trans/
qed.

lemma fle_flat_dx_dx: ∀L1,L2,T1,T2. ⦃L1, T1⦄ ⊆ ⦃L2, T2⦄ →
                      ∀I,V2. ⦃L1, T1⦄ ⊆ ⦃L2, ⓕ{I}V2.T2⦄.
#L1 #L2 #T1 #T2 * #n1 #m1 #f2 #g2 #Hf2 #Hg2 #HL12 #Hfg2 #I #V2
elim (frees_total L2 V2) #g1 #Hg1
elim (sor_isfin_ex g1 g2) /2 width=3 by frees_fwd_isfin/ #g #Hg #_
@(ex4_4_intro … g Hf2 … HL12) (**) (* full auto too slow *)
/4 width=5 by frees_flat, sor_inv_sle_dx, sor_tls, sle_trans/
qed.
