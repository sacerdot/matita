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

include "basic_2/substitution/drop_leq.ma".
include "basic_2/multiple/frees.ma".

(* CONTEXT-SENSITIVE FREE VARIABLES *****************************************)

(* Properties on equivalence for local environments *************************)

lemma leq_frees_trans: ∀L2,U,d,i. L2 ⊢ i ϵ 𝐅*[d]⦃U⦄ →
                       ∀L1. L1 ⩬[d, ∞] L2 → L1 ⊢ i ϵ 𝐅*[d]⦃U⦄.
#L2 #U #d #i #H elim H -L2 -U -d -i /3 width=2 by frees_eq/
#I2 #L2 #K2 #U #W2 #d #i #j #Hdj #Hji #HnU #HLK2 #_ #IHW2 #L1 #HL12
elim (leq_drop_trans_be … HL12 … HLK2) -L2 // >yminus_Y_inj #K1 #HK12 #HLK1
lapply (leq_inv_O_Y … HK12) -HK12 #H destruct /3 width=9 by frees_be/
qed-.

lemma frees_leq_conf: ∀L1,U,d,i. L1 ⊢ i ϵ 𝐅*[d]⦃U⦄ →
                      ∀L2. L1 ⩬[d, ∞] L2 → L2 ⊢ i ϵ 𝐅*[d]⦃U⦄.
/3 width=3 by leq_sym, leq_frees_trans/ qed-.
