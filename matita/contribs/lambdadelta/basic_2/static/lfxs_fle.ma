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
include "basic_2/static/fle.ma".
include "basic_2/static/lfxs_lfxs.ma".

(* GENERIC EXTENSION ON REFERRED ENTRIES OF A CONTEXT-SENSITIVE REALTION ****)

(* Properties with free variables inclusion for restricted closures *********)

lemma fle_lfxs_trans: ∀R,L1,T1,T2. ⦃L1, T1⦄ ⊆ ⦃L1, T2⦄ →
                      ∀L2. L1 ⪤*[R, T2] L2 → L1 ⪤*[R, T1] L2.
#R #L1 #T1 #T2 * #f1 #f2 #Hf1 #Hf2 #Hf12 #L2 #HL12
/4 width=5 by lfxs_inv_frees, sle_lexs_trans, ex2_intro/
qed-.
