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

include "Basic_2/unfold/ltpss_ltpss.ma".
include "Basic_2/reducibility/cpr.ma".

(* CONTEXT-SENSITIVE PARALLEL REDUCTION ON TERMS ****************************)

(* Advanced inversion lemmas ************************************************)

(* Basic_1: was pr2_gen_abbr *)
lemma cpr_inv_abbr1: ∀L,V1,T1,U2. L ⊢ ⓓV1. T1 ➡ U2 →
                     (∃∃V2,T2,T. L ⊢ V1 ➡ V2 & L. ⓓV2 ⊢ T1 ➡ T2 &
                                 L.  ⓓV2 ⊢ T [1, |L|] ▶* T2 &
                                 U2 = ⓓV2. T
                      ) ∨
                      ∃∃T. ⇧[0,1] T ≡ T1 & L ⊢ T ➡ U2.
#L #V1 #T1 #Y * #X #H1 #H2
elim (tpr_inv_abbr1 … H1) -H1 *
[ #V #T0 #T #HV1 #HT10 #HT0 #H destruct
  elim (tpss_inv_bind1 … H2) -H2 #V2 #T2 #HV2 #HT2 #H destruct
  lapply (tps_lsubs_conf … HT0 (L. ⓓV) ?) -HT0 /2 width=1/ #HT0
  elim (ltpss_tps_conf … HT0 (L. ⓓV2) 1 (|L|) ?) -HT0 /2 width=1/ #V0 #HV20 #HV0
  lapply (tpss_weak_all … HV20) -HV20 #HV20
  lapply (tpss_lsubs_conf … HV0 (L. ⓓV2) ?) -HV0 /2 width=1/ #HV0
  elim (tpss_conf_eq … HT2 … HV0) -T #T3 #HT23 #HVT3
  lapply (tpss_weak_all … HVT3) -HVT3 #HVT3
  lapply (tpss_trans_eq … HV20 … HVT3) -V0 /4 width=7/
| /4 width=5/
]
qed-.
