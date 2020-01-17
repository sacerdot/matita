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

include "basic_2A/substitution/drop_lreq.ma".
include "basic_2A/multiple/frees.ma".

(* CONTEXT-SENSITIVE FREE VARIABLES *****************************************)

(* Properties on equivalence for local environments *************************)

lemma lreq_frees_trans: ∀L2,U,l,i. L2 ⊢ i ϵ 𝐅*[l]⦃U⦄ →
                        ∀L1. L1 ⩬[l, ∞] L2 → L1 ⊢ i ϵ 𝐅*[l]⦃U⦄.
#L2 #U #l #i #H elim H -L2 -U -l -i /3 width=2 by frees_eq/
#I2 #L2 #K2 #U #W2 #l #i #j #Hlj #Hji #HnU #HLK2 #_ #IHW2 #L1 #HL12
elim (lreq_drop_trans_be … HL12 … HLK2) -L2 // >yminus_Y_inj #K1 #HK12 #HLK1
lapply (lreq_inv_O_Y … HK12) -HK12 #H destruct /3 width=9 by frees_be/
qed-.

lemma frees_lreq_conf: ∀L1,U,l,i. L1 ⊢ i ϵ 𝐅*[l]⦃U⦄ →
                       ∀L2. L1 ⩬[l, ∞] L2 → L2 ⊢ i ϵ 𝐅*[l]⦃U⦄.
/3 width=3 by lreq_sym, lreq_frees_trans/ qed-.
