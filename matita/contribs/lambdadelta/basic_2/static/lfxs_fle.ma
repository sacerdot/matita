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

(* include "basic_2/syntax/lveq_length.ma". *)
include "basic_2/static/fle.ma".
include "basic_2/static/lfxs_lfxs.ma".

(* GENERIC EXTENSION ON REFERRED ENTRIES OF A CONTEXT-SENSITIVE REALTION ****)
(*
lemma pippo: ∀L1,L2,n1,n2. L1 ≋ⓧ*[n1, n2] L2 →
             ∀T,f. L1 ⊢ 𝐅*⦃T⦄ ≡ f → ∃g. ↑*[n1]g = f. 
*)
(* Properties with free variables inclusion for restricted closures *********)
(*
lemma fle_lfxs_trans: ∀R,L1,T1,T2. ⦃L1, T1⦄ ⊆ ⦃L1, T2⦄ →
                      ∀L2. L1 ⪤*[R, T2] L2 → L1 ⪤*[R, T1] L2.
#R #L1 #T1 #T2 * #x #n #f1 #f2 #Hf1 #Hf2 #Hn #Hf #L2 #HL12
lapply (lveq_inj_length … Hn ?) // #H destruct


 Hn : (L1≋ⓧ*[n,n]L1) (L1⊢𝐅*⦃T1⦄≡f1) → 

lapply (lfxs_inv_frees … HL12 … Hf2) -HL12 -Hf2 #HL12
@(ex2_intro … Hf1) -Hf1
@(sle_lexs_trans … HL12) -HL12 //

/4 width=5 by lfxs_inv_frees, sle_lexs_trans, ex2_intro/
qed-.
*)