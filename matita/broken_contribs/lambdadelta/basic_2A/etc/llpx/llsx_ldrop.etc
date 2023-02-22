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

include "basic_2/substitution/lleq_ldrop.ma".
include "basic_2/computation/llsx.ma".

(* LAZY SN EXTENDED STRONGLY NORMALIZING LOCAL ENVIRONMENTS *****************)

(* Advanced properties ******************************************************)

lemma llsx_lref_free: ∀h,g,G,L,d,i. |L| ≤ i → G ⊢ ⋕⬊*[h, g, #i, d] L.
#h #g #G #L1 #d #i #HL1 @llsx_intro
#L2 #HL12 #H elim H -H
/4 width=8 by llpx_fwd_length, lleq_free, le_repl_sn_conf_aux/
qed.

lemma llsx_lref_skip: ∀h,g,G,L,d,i. yinj i < d → G ⊢ ⋕⬊*[h, g, #i, d] L.
#h #g #G #L1 #d #i #HL1 @llsx_intro
#L2 #HL12 #H elim H -H
/3 width=6 by llpx_fwd_length, lleq_skip/
qed.
