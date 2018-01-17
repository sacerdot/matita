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
include "basic_2/static/fle.ma".
include "basic_2/static/lfxs_lfxs.ma".

(* GENERIC EXTENSION ON REFERRED ENTRIES OF A CONTEXT-SENSITIVE REALTION ****)

(* Properties with free variables inclusion for restricted closures *********)

(* Note: we just need lveq_inv_refl: ∀L,n1,n2. L ≋ⓧ*[n1, n2] L → ∧∧ 0 = n1 & 0 = n2 *)
lemma fle_lfxs_trans: ∀R,L1,T1,T2. ⦃L1, T1⦄ ⊆ ⦃L1, T2⦄ →
                      ∀L2. L1 ⪤*[R, T2] L2 → L1 ⪤*[R, T1] L2.
#R #L1 #T1 #T2 * #n1 #n2 #f1 #f2 #Hf1 #Hf2 #Hn #Hf #L2 #HL12
elim (lveq_inj_length … Hn ?) // #H1 #H2 destruct
/4 width=5 by lfxs_inv_frees, sle_lexs_trans, ex2_intro/
qed-.
