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
include "basic_2/static/frees_drops.ma".
include "basic_2/static/fle.ma".

(* FREE VARIABLES INCLUSION FOR RESTRICTED CLOSURES *************************)

(* Advanced properties ******************************************************)

lemma fle_lifts_sn: ∀T1,U1. ⬆*[1] T1 ≡ U1 → ∀L1,L2. |L2| ≤ |L1| →
                    ∀T2. ⦃L1, T1⦄ ⊆ ⦃L2, T2⦄ → ⦃L1.ⓧ, U1⦄ ⊆ ⦃L2, T2⦄.
#T1 #U1 #HTU1 #L1 #L2 #H1L #T2
* #n #m #f #g #Hf #Hg #H2L #Hfg
lapply (lveq_length_fwd_dx … H2L ?) // -H1L #H destruct
lapply (frees_lifts_SO (Ⓣ) (L1.ⓧ) … HTU1 … Hf)
[ /3 width=4 by drops_refl, drops_drop/ ] -T1 #Hf
@(ex4_4_intro … Hf Hg) /2 width=4 by lveq_void_sn/ (**) (* explict constructor *)
qed-.

(* Advanced inversion lemmas ************************************************)

lemma fle_inv_lifts_sn: ∀T1,U1. ⬆*[1] T1 ≡ U1 →
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
