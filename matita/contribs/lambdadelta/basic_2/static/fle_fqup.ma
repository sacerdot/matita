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
include "basic_2/static/fle.ma".

(* FREE VARIABLES INCLUSION FOR RESTRICTED CLOSURES *************************)

(* Advanced properties ******************************************************)
(*
lemma fle_refl: bi_reflexive … fle.
#L #T elim (frees_total L T) /2 width=5 by sle_refl, ex3_2_intro/
qed.
*)
lemma fle_bind_dx_sn: ∀L1,L2,V1,V2. ⦃L1, V1⦄ ⊆ ⦃L2, V2⦄ →
                      ∀p,I,T2. ⦃L1, V1⦄ ⊆ ⦃L2, ⓑ{p,I}V2.T2⦄.
#L1 #L2 #V1 #V2 * -L1 #f1 #g1 #L1 #n #Hf1 #Hg1 #HL12 #Hfg1 #p #I #T2
elim (frees_total (L2.ⓧ) T2) #g2 #Hg2
elim (sor_isfin_ex g1 (⫱g2)) /3 width=3 by frees_fwd_isfin, isfin_tl/ #g #Hg #_
/4 width=8 by fle_intro, frees_bind_void, sor_inv_sle_sn, sle_trans/
qed.
(*
lemma fle_bind_dx_dx: ∀L1,L2,T1,T2. ⦃L1.ⓧ, T1⦄ ⊆ ⦃L2.ⓧ, T2⦄ →
                      ∀p,I,V2. ⦃L1.ⓧ, T1⦄ ⊆ ⦃L2, ⓑ{p,I}V2.T2⦄.
#L1 #L2 #T1 #T2 * -L1 #f2 #g2 #L1 #n #Hf2 #Hg2 #HL12 #Hfg2 #p #I #V2
elim (frees_total L2 V2) #g1 #Hg1
elim (sor_isfin_ex g1 (⫱g2)) /3 width=3 by frees_fwd_isfin, isfin_tl/ #g #Hg #_
@(fle_intro … g … Hf2) /2 width=5 by frees_bind_void/
@(sle_trans … Hfg1) @(sor_inv_sle_sn … Hg)



/4 width=8 by fle_intro, frees_bind_void, sor_inv_sle_dx, sle_trans/
qed.
*)
lemma fle_flat_dx_sn: ∀L1,L2,V1,V2. ⦃L1, V1⦄ ⊆ ⦃L2, V2⦄ →
                      ∀I,T2. ⦃L1, V1⦄ ⊆ ⦃L2, ⓕ{I}V2.T2⦄.
#L1 #L2 #V1 #V2 * -L1 #f1 #g1 #L1 #n #Hf1 #Hg1 #HL12 #Hfg1 #I #T2
elim (frees_total L2 T2) #g2 #Hg2
elim (sor_isfin_ex g1 g2) /2 width=3 by frees_fwd_isfin/ #g #Hg #_
/4 width=8 by fle_intro, frees_flat, sor_inv_sle_sn, sle_trans/
qed.

lemma fle_flat_dx_dx: ∀L1,L2,T1,T2. ⦃L1, T1⦄ ⊆ ⦃L2, T2⦄ →
                      ∀I,V2. ⦃L1, T1⦄ ⊆ ⦃L2, ⓕ{I}V2.T2⦄.
#L1 #L2 #T1 #T2 * -L1 #f2 #g2 #L1 #n #Hf2 #Hg2 #HL12 #Hfg2 #I #V2
elim (frees_total L2 V2) #g1 #Hg1
elim (sor_isfin_ex g1 g2) /2 width=3 by frees_fwd_isfin/ #g #Hg #_
/4 width=8 by fle_intro, frees_flat, sor_inv_sle_dx, sle_trans/
qed.
