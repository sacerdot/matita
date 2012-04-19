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

include "basic_2/unfold/ltpsss.ma".
include "basic_2/reducibility/ltpr_ltpss.ma".

(* CONTEXT-FREE PARALLEL REDUCTION ON LOCAL ENVIRONMENTS ********************)

(* Properties on iterated parallel unfold on local environments *************)

lemma ltpr_ltpsss_conf: ∀L1,K1,d,e. L1 [d, e] ▶** K1 → ∀L2. L1 ➡ L2 →
                        ∃∃K2. L2 [d, e] ▶** K2 & K1 ➡ K2.
#L1 #K1 #d #e #H @(ltpsss_ind … H) -K1 /2 width=3/
#K #K1 #_ #HK1 #IHK #L2 #HL12
elim (IHK … HL12) -L1 #K2 #HLK2 #HK2
elim (ltpr_ltpss_conf … HK1 … HK2) -K /3 width=3/
qed.
