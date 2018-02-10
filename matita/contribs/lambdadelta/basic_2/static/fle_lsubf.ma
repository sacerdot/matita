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

include "basic_2/static/frees_fqup.ma".
include "basic_2/static/lsubf_lsubr.ma".
include "basic_2/static/fle.ma".

(* FREE VARIABLES INCLUSION FOR RESTRICTED CLOSURES *************************)

(* Advanced forward lemmas ***************************************************)

lemma fle_fwd_pair_sn: ∀I1,I2,L1,L2,V1,V2,T1,T2. ⦃L1.ⓑ{I1}V1, T1⦄ ⊆ ⦃L2.ⓑ{I2}V2, T2⦄ →
                       ⦃L1.ⓧ, T1⦄ ⊆ ⦃L2.ⓑ{I2}V2, T2⦄.
#I1 #I2 #L1 #L2 #V1 #V2 #T1 #T2 *
#n1 #n2 #f1 #f2 #Hf1 #Hf2 #HL12 #Hf12
elim (lveq_inv_pair_pair … HL12) -HL12 #HL12 #H1 #H2 destruct
elim (frees_total (L1.ⓧ) T1) #g1 #Hg1
lapply (lsubr_lsubf … Hg1 … Hf1) -Hf1 /2 width=1 by lsubr_unit/ #Hfg1
/5 width=10 by lsubf_fwd_sle, lveq_bind, sle_trans, ex4_4_intro/ (**) (* full auto too slow *)
qed-.
