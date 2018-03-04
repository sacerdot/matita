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

include "basic_2/static/frees_drops.ma".
include "basic_2/static/fsle_length.ma".

(* FREE VARIABLES INCLUSION FOR RESTRICTED CLOSURES *************************)

(* Advanced properties ******************************************************)

lemma fsle_lifts_sn: ∀T1,U1. ⬆*[1] T1 ≡ U1 → ∀L1,L2. |L2| ≤ |L1| →
                     ∀T2. ⦃L1, T1⦄ ⊆ ⦃L2, T2⦄ → ⦃L1.ⓧ, U1⦄ ⊆ ⦃L2, T2⦄.
#T1 #U1 #HTU1 #L1 #L2 #H1L #T2
* #n #m #f #g #Hf #Hg #H2L #Hfg
lapply (lveq_length_fwd_dx … H2L ?) // -H1L #H destruct
lapply (frees_lifts_SO (Ⓣ) (L1.ⓧ) … HTU1 … Hf)
[ /3 width=4 by drops_refl, drops_drop/ ] -T1 #Hf
@(ex4_4_intro … Hf Hg) /2 width=4 by lveq_void_sn/ (**) (* explict constructor *)
qed-.

lemma fsle_lifts_SO_sn: ∀K1,K2. |K1| = |K2| → ∀V1,V2. ⦃K1, V1⦄ ⊆ ⦃K2, V2⦄ →
                        ∀W1. ⬆*[1] V1 ≡ W1 → ∀I1,I2. ⦃K1.ⓘ{I1}, W1⦄ ⊆ ⦃K2.ⓑ{I2}V2, #O⦄.
#K1 #K2 #HK #V1 #V2
* #n1 #n2 #f1 #f2 #Hf1 #Hf2 #HK12 #Hf12
#W1 #HVW1 #I1 #I2
elim (lveq_inj_length … HK12) // -HK #H1 #H2 destruct
/5 width=12 by frees_lifts_SO, frees_pair, drops_refl, drops_drop, lveq_bind, sle_weak, ex4_4_intro/
qed.

lemma fsle_lifts_SO: ∀K1,K2. |K1| = |K2| → ∀T1,T2. ⦃K1, T1⦄ ⊆ ⦃K2, T2⦄ →
                     ∀U1,U2. ⬆*[1] T1 ≡ U1 → ⬆*[1] T2 ≡ U2 →
                     ∀I1,I2.  ⦃K1.ⓘ{I1}, U1⦄ ⊆ ⦃K2.ⓘ{I2}, U2⦄.
#K1 #K2 #HK #T1 #T2
* #n1 #n2 #f1 #f2 #Hf1 #Hf2 #HK12 #Hf12
#U1 #U2 #HTU1 #HTU2 #I1 #I2
elim (lveq_inj_length … HK12) // -HK #H1 #H2 destruct
/5 width=12 by frees_lifts_SO, drops_refl, drops_drop, lveq_bind, sle_push, ex4_4_intro/
qed.

(* Advanced inversion lemmas ************************************************)

lemma fsle_inv_lifts_sn: ∀T1,U1. ⬆*[1] T1 ≡ U1 →
                         ∀I1,I2,L1,L2,V1,V2,U2. ⦃L1.ⓑ{I1}V1,U1⦄ ⊆ ⦃L2.ⓑ{I2}V2, U2⦄ →
                         ∀p. ⦃L1, T1⦄ ⊆ ⦃L2, ⓑ{p,I2}V2.U2⦄.
#T1 #U1 #HTU1 #I1 #I2 #L1 #L2 #V1 #V2 #U2
* #n #m #f2 #g2 #Hf2 #Hg2 #HL #Hfg2 #p
elim (lveq_inv_pair_pair … HL) -HL #HL #H1 #H2 destruct
elim (frees_total L2 V2) #g1 #Hg1
elim (sor_isfin_ex g1 (⫱g2)) /3 width=3 by frees_fwd_isfin, isfin_tl/ #g #Hg #_
lapply (frees_inv_lifts_SO (Ⓣ) … Hf2 … HTU1)
[1,2: /3 width=4 by drops_refl, drops_drop/ ] -U1 #Hf2
lapply (sor_inv_sle_dx … Hg) #H0g
/5 width=10 by frees_bind, sle_tl, sle_trans, ex4_4_intro/
qed-.
