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

include "basic_2/rt_transition/cpx_simple.ma".
include "basic_2/rt_computation/csx_csx.ma".

(* STRONGLY NORMALIZING TERMS FOR EXTENDED PARALLEL RT-TRANSITION ***********)

(* Properties with simple terms *********************************************)

lemma csx_appl_simple (G) (L):
      ∀V. ❪G,L❫ ⊢ ⬈*𝐒 V → ∀T1.
      (∀T2. ❪G,L❫ ⊢ T1 ⬈ T2 → (T1 ≅ T2 → ⊥) → ❪G,L❫ ⊢ ⬈*𝐒 ⓐV.T2) →
      𝐒❪T1❫ → ❪G,L❫ ⊢ ⬈*𝐒 ⓐV.T1.
#G #L #V #H @(csx_ind … H) -V
#V #_ #IHV #T1 #IHT1 #HT1
@csx_intro #X #H1 #H2
elim (cpx_inv_appl1_simple … H1) // -H1
#V0 #T0 #HLV0 #HLT10 #H destruct
elim (tneqx_inv_pair … H2) -H2
[ #H elim H -H //
| #HV0 @(csx_cpx_trans … (ⓐV0.T1)) /2 width=1 by cpx_flat/ -HLT10
  @(IHV … HLV0 … HV0) -HV0 /4 width=5 by csx_cpx_trans, cpx_pair_sn/ (**) (* full auto too slow *)
| -IHV -HT1 /4 width=3 by csx_cpx_trans, cpx_pair_sn/
]
qed.
