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

include "basic_2/computation/lpxs_lleq.ma".
include "basic_2/computation/lsx.ma".

(* SN EXTENDED STRONGLY NORMALIZING LOCAL ENVIRONMENTS **********************)

(* Advanced properties ******************************************************)

lemma lsx_lleq_trans: ∀h,g,T,G,L1. G ⊢ ⋕⬊*[h, g, T] L1 →
                      ∀L2. L1 ⋕[T, 0] L2 → G ⊢ ⋕⬊*[h, g, T] L2.
#h #g #T #G #L1 #H @(lsx_ind … H) -L1 #L1 #HL1 #IHL1 #L2 #HL12
@lsx_intro #L #HL2 #HnT elim (lleq_lpxs_trans_nlleq … HL12 … HL2 HnT) -L2 /3 width=4 by/
qed-.

lemma lsx_lpxs_trans: ∀h,g,T,G,L1. G ⊢ ⋕⬊*[h, g, T] L1 →
                      ∀L2. ⦃G, L1⦄ ⊢ ➡*[h, g] L2 → G ⊢ ⋕⬊*[h, g, T] L2.
#h #g #T #G #L1 #H @(lsx_ind … H) -L1 #L1 #HL1 #IHL1 #L2 #HL12
elim (lleq_dec T L1 L2 0) /3 width=4 by lsx_lleq_trans/
qed-.
