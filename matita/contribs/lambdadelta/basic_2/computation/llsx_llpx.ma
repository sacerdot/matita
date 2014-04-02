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

include "basic_2/substitution/lleq_lleq.ma".
include "basic_2/reduction/llpx_lleq.ma".
include "basic_2/computation/llsx.ma".

(* SN EXTENDED STRONGLY NORMALIZING LOCAL ENVIRONMENTS **********************)

(* Advanced properties ******************************************************)

lemma llsx_llpx_trans: ∀h,g,G,L1,T,d. G ⊢ ⋕⬊*[h, g, T, d] L1 →
                       ∀L2. ⦃G, L1⦄ ⊢ ➡[h, g, T, d] L2 → G ⊢ ⋕⬊*[h, g, T, d] L2.
#h #g #G #L1 #T #d #H @(llsx_ind … H) -L1 #L1 #HL1 #IHL1 #L2 #HL12 @llsx_intro
elim (lleq_dec T L1 L2 d) /4 width=4 by lleq_llpx_trans, lleq_canc_sn/
qed-.
