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

include "basic_2/rt_transition/rpx_reqx.ma".
include "basic_2/rt_transition/cnx.ma".

(* NORMAL TERMS FOR EXTENDED CONTEXT-SENSITIVE PARALLEL RT-TRANSITION *******)

(* Advanced properties ******************************************************)

lemma cnx_teqx_trans (G) (L):
      ∀T1. ❪G,L❫ ⊢ ⬈𝐍 T1 → ∀T2. T1 ≛ T2 → ❪G,L❫ ⊢ ⬈𝐍 T2.
#G #L #T1 #HT1 #T2 #HT12 #T #HT2
elim (teqx_cpx_trans … HT12 … HT2) -HT2 #T0 #HT10 #HT0
lapply (HT1 … HT10) -HT1 -HT10 /2 width=5 by teqx_repl/ (**) (* full auto fails *)
qed-.
