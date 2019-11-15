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

include "static_2/syntax/teqo_simple.ma".
include "static_2/syntax/teqo_teqo.ma".
include "basic_2/rt_transition/cpx_simple.ma".
include "basic_2/rt_computation/cpxs.ma".
include "basic_2/rt_computation/csx_csx.ma".

(* STRONGLY NORMALIZING TERMS FOR UNBOUND PARALLEL RT-TRANSITION ************)

(* Properties with outer equivalence for terms ******************************)

(* Basic_1: was just: sn3_appl_appl *)
(* Basic_2A1: was: csx_appl_simple_tsts *)
lemma csx_appl_simple_teqo (h) (G) (L):
      ∀V. ⦃G,L⦄ ⊢ ⬈*[h] 𝐒⦃V⦄ → ∀T1. ⦃G,L⦄ ⊢ ⬈*[h] 𝐒⦃T1⦄ →
      (∀T2. ⦃G,L⦄ ⊢ T1 ⬈*[h] T2 → (T1 ⩳ T2 → ⊥) → ⦃G,L⦄ ⊢ ⬈*[h] 𝐒⦃ⓐV.T2⦄) →
      𝐒⦃T1⦄ → ⦃G,L⦄ ⊢ ⬈*[h] 𝐒⦃ⓐV.T1⦄.
#h #G #L #V #H @(csx_ind … H) -V
#V #_ #IHV #T1 #H @(csx_ind … H) -T1
#T1 #H1T1 #IHT1 #H2T1 #H3T1
@csx_intro #X #HL #H
elim (cpx_inv_appl1_simple … HL) -HL //
#V0 #T0 #HLV0 #HLT10 #H0 destruct
elim (tdneq_inv_pair … H) -H
[ #H elim H -H //
| -IHT1 #HV0
  @(csx_cpx_trans … (ⓐV0.T1)) /2 width=1 by cpx_flat/ -HLT10
  @IHV -IHV /4 width=3 by csx_cpx_trans, cpx_pair_sn/
| -IHV -H1T1 #H1T10
  @(csx_cpx_trans … (ⓐV.T0)) /2 width=1 by cpx_flat/ -HLV0
  elim (teqo_dec T1 T0) #H2T10
  [ @IHT1 -IHT1 /4 width=5 by cpxs_strap2, cpxs_strap1, teqo_canc_sn, simple_teqo_repl_dx/
  | -IHT1 -H3T1 -H1T10 /3 width=1 by cpx_cpxs/
  ]
]
qed.
