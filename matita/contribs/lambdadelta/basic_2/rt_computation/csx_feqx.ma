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

include "static_2/static/feqx.ma".
include "basic_2/rt_computation/csx_reqx.ma".

(* STRONGLY NORMALIZING TERMS FOR UNBOUND PARALLEL RT-TRANSITION ************)

(* Properties with sort-irrelevant equivalence for closures *****************)

lemma csx_feqx_conf: ∀h,G1,L1,T1. ❪G1,L1❫ ⊢ ⬈*[h] 𝐒❪T1❫ →
                     ∀G2,L2,T2. ❪G1,L1,T1❫ ≛ ❪G2,L2,T2❫ → ❪G2,L2❫ ⊢ ⬈*[h] 𝐒❪T2❫.
#h #G1 #L1 #T1 #HT1 #G2 #L2 #T2 * -G2 -L2 -T2
/3 width=3 by csx_reqx_conf, csx_teqx_trans/
qed-.
