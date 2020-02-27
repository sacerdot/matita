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

include "basic_2/grammar/lpx_sn_lpx_sn.ma".
include "basic_2/substitution/fsupp.ma".
include "basic_2/unfold/lpqs_ldrop.ma".

(* SN RESTRICTED PARALLEL COMPUTATION FOR LOCAL ENVIRONMENTS ****************)

(* Main properties on context-sensitive rest parallel computation for terms *)

theorem cpqs_trans_lpqs: lpx_sn_transitive cpqs cpqs.
#L0 #T0 @(fsupp_wf_ind … L0 T0) -L0 -T0 #L0 #T0 #IH #L1 * [|*]
[ #I #HL #HT #T #H1 #L2 #HL12 #T2 #HT2 destruct
  elim (cpqs_inv_atom1 … H1) -H1
  [ #H destruct
    elim (cpqs_inv_atom1 … HT2) -HT2
    [ #H destruct //
    | * #K2 #V #V2 #i #HLK2 #HV2 #HVT2 #H destruct
      elim (lpqs_ldrop_trans_O1 … HL12 … HLK2) -L2 #X #HLK1 #H
      elim (lpqs_inv_pair2 … H) -H #K1 #V1 #HK12 #HV1 #H destruct
      lapply (fsupp_lref … HLK1) /3 width=9/
    ]
  | * #K1 #V1 #V #i #HLK1 #HV1 #HVT #H destruct
    elim (lpqs_ldrop_conf … HLK1 … HL12) -HL12 #X #H #HLK2
    elim (lpqs_inv_pair1 … H) -H #K2 #W2 #HK12 #_ #H destruct
    lapply (ldrop_fwd_ldrop2 … HLK2) -W2 #HLK2
    elim (cpqs_inv_lift1 … HT2 … HLK2 … HVT) -L2 -T
    lapply (fsupp_lref … HLK1) /3 width=9/
  ]
| #a #I #V1 #T1 #HL #HT #X1 #H1 #L2 #HL12 #X2 #H2
  elim (cpqs_inv_bind1 … H1) -H1 *
  [ #V #T #HV1 #HT1 #H destruct
    elim (cpqs_inv_bind1 … H2) -H2 *
    [ #V2 #T2 #HV2 #HT2 #H destruct /4 width=5/
    | #T2 #HT2 #HXT2 #H1 #H2 destruct /4 width=5/
    ]
  | #Y1 #HTY1 #HXY1 #H11 #H12 destruct
    elim (lift_total X2 0 1) #Y2 #HXY2
    lapply (cpqs_lift … H2 (L2.ⓓV1) … HXY1 … HXY2) /2 width=1/ -X1 /4 width=5/
  ]
| #I #V1 #T1 #HL #HT #X1 #H1 #L2 #HL12 #X2 #H2
  elim (cpqs_inv_flat1 … H1) -H1 *
  [ #V #T #HV1 #HT1 #H destruct
    elim (cpqs_inv_flat1 … H2) -H2 *
    [ #V2 #T2 #HV2 #HT2 #H destruct /3 width=5/
    | #HX2 #H destruct /3 width=5/
    ]
  | #HX1 #H destruct /3 width=5/
]
qed-.

theorem cpqs_trans: ∀L. Transitive … (cpqs L).
/2 width=5 by cpqs_trans_lpqs/ qed-.

(* Properties on context-sensitive rest. parallel computation for terms *****)

lemma lpqs_cpqs_trans: ∀L1,L2. L1 ⊢ ➤* L2 →
                       ∀T1,T2. L2 ⊢ T1 ➤* T2 → L1 ⊢ T1 ➤* T2.
/2 width=5 by cpqs_trans_lpqs/ qed-.
