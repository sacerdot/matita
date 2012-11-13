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

include "basic_2/reducibility/xpr_lsubss.ma".
include "basic_2/computation/xprs.ma".

(* EXTENDED PARALLEL COMPUTATION ON TERMS ***********************************)

(* Properties on lenv ref for stratified type assignment ********************)

lemma lsubss_xprs_trans: ∀h,g,L1,L2. h ⊢ L1 •⊑[g] L2 →
                         ∀T1,T2. ⦃h, L2⦄ ⊢ T1 •➡*[g] T2 → ⦃h, L1⦄ ⊢ T1 •➡*[g] T2.
#h #g #L1 #L2 #HL12 #T1 #T2 #H @(xprs_ind … H) -T2 //
#T #T2 #_ #HT2 #IHT1
lapply (lsubss_xpr_trans … HL12 … HT2) -L2 /2 width=3/
qed-.
