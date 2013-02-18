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

include "basic_2/dynamic/snv_fpr.ma".

(* STRATIFIED NATIVE VALIDITY FOR TERMS *************************************)

(* Properties on context-free parallel computation for closures *************)

fact ssta_fprs_aux: ∀h,g,n. (
                       ∀L,T2. ♯{L,T2} < n →
                       ∀T1. L ⊢ T1 ⬌* T2 → ⦃h, L⦄ ⊩ T1 :[g] → ⦃h, L⦄ ⊩ T2 :[g] →
                       ∀U1,l1. ⦃h, L⦄ ⊢ T1 •[g, l1] U1 →
                       ∀U2,l2. ⦃h, L⦄ ⊢ T2 •[g, l2] U2 →
                       L ⊢ U1 ⬌* U2 ∧ l1 = l2
                    ) → (
                       ∀L,T. ♯{L,T} < n → ⦃h, L⦄ ⊩ T :[g] →
                       ∀U. ⦃h, L⦄ ⊢ T •*➡*[g] U → ⦃h, L⦄ ⊩ U :[g]
                    ) → (
                       ∀L1,T1. ♯{L1,T1} < n →
                       ∀U1,l. ⦃h, L1⦄ ⊢ T1 •[g, l] U1 →
                       ∀L2,T2. ⦃L1, T1⦄ ➡* ⦃L2, T2⦄ →  ⦃h, L1⦄ ⊩ T1 :[g] →
                       ∃∃U2. ⦃h, L2⦄ ⊢ T2 •[g, l] U2 & ⦃L1, U1⦄ ⬌* ⦃L2, U2⦄
                    ) →
                    ∀L1,T1. ♯{L1,T1} = n →
                    ∀U1,l. ⦃h, L1⦄ ⊢ T1 •[g, l] U1 →
                    ∀L2,T2. ⦃L1, T1⦄ ➡* ⦃L2, T2⦄ → ⦃h, L1⦄ ⊩ T1 :[g] →
                    ∃∃U2. ⦃h, L2⦄ ⊢ T2 •[g, l] U2 & ⦃L1, U1⦄ ⬌* ⦃L2, U2⦄.
#h #g #n #IH3 #IH2 #IH1 #L1 #T1 #Hn #U1 #l #HTU1 #L2 #T2 #H12 #HT1
@(fprs_ind … H12) -L2 -T2 [-IH1 /2 width=3/ ] (**) (* auto fails without -IH1 *)
#L #L2 #T #T2 #HT1 #HT2 * #U #HTU #HU1
(*
lapply (IH2 … 

elim (ssta_fpr_aux … IH3 … Hn … HTU1 … HT2 HT1)
-T1 -IH3 -IH2 -HL1 [2: /3 width=5/ ] -n #U #HTU #HU1 
*)