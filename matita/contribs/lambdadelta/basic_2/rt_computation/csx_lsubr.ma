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

include "basic_2/rt_transition/cpx_lsubr.ma".
include "basic_2/rt_computation/csx_csx.ma".

(* STRONGLY NORMALIZING TERMS FOR EXTENDED PARALLEL RT-TRANSITION ***********)

(* Advanced properties ******************************************************)

fact csx_appl_beta_aux (G) (L):
     ∀p,U1. ❪G,L❫ ⊢ ⬈*𝐒 U1 →
     ∀V,W,T1. U1 = ⓓ[p]ⓝW.V.T1 → ❪G,L❫ ⊢ ⬈*𝐒 ⓐV.ⓛ[p]W.T1.
#G #L #p #X #H @(csx_ind … H) -X
#X #HT1 #IHT1 #V #W #T1 #H1 destruct
@csx_intro #X #H1 #H2
elim (cpx_inv_appl1 … H1) -H1 *
[ -HT1 #V0 #Y #HLV0 #H #H0 destruct
  elim (cpx_inv_abst1 … H) -H #W0 #T0 #HLW0 #HLT0 #H destruct
  @IHT1 -IHT1 [4: // | skip ]
  [ lapply (lsubr_cpx_trans … HLT0 (L.ⓓⓝW.V) ?) -HLT0 -H2
    /3 width=1 by cpx_bind, cpx_flat, lsubr_beta/
  | #H elim (teqx_inv_pair … H) -H
    #_ #H elim (teqx_inv_pair … H) -H
    #_ /4 width=1 by teqx_pair/
  ]
| -IHT1 -H2 #q #V0 #W0 #W2 #T0 #T2 #HLV0 #HLW02 #HLT02 #H1 #H3 destruct
  lapply (lsubr_cpx_trans … HLT02 (L.ⓓⓝW0.V) ?) -HLT02
  /4 width=5 by csx_cpx_trans, cpx_bind, cpx_flat, lsubr_beta/
| -HT1 -IHT1 -H2 #q #V0 #V1 #W0 #W1 #T0 #T3 #_ #_ #_ #_ #H destruct
]
qed-.

(* Basic_1: was just: sn3_beta *)
lemma csx_appl_beta (G) (L):
      ∀p,V,W,T. ❪G,L❫ ⊢ ⬈*𝐒 ⓓ[p]ⓝW.V.T → ❪G,L❫ ⊢ ⬈*𝐒 ⓐV.ⓛ[p]W.T.
/2 width=3 by csx_appl_beta_aux/ qed.

(* Advanced forward lemmas **************************************************)

fact csx_fwd_bind_dx_unit_aux (G) (L):
     ∀U. ❪G,L❫ ⊢ ⬈*𝐒 U →
     ∀p,I,J,V,T. U = ⓑ[p,I]V.T → ❪G,L.ⓤ[J]❫ ⊢ ⬈*𝐒 T.
#G #L #U #H elim H -H #U0 #_ #IH #p #I #J #V #T #H destruct
@csx_intro #T2 #HLT2 #HT2
@(IH (ⓑ[p, I]V.T2)) -IH /2 width=4 by cpx_bind_unit/ -HLT2 #H
elim (teqx_inv_pair … H) -H /2 width=1 by/
qed-.

lemma csx_fwd_bind_dx_unit (G) (L):
      ∀p,I,V,T. ❪G,L❫ ⊢ ⬈*𝐒 ⓑ[p,I]V.T →
      ∀J. ❪G,L.ⓤ[J]❫ ⊢ ⬈*𝐒 T.
/2 width=6 by csx_fwd_bind_dx_unit_aux/ qed-.

lemma csx_fwd_bind_unit (G) (L):
      ∀p,I,V,T. ❪G,L❫ ⊢ ⬈*𝐒 ⓑ[p,I]V.T →
      ∀J. ∧∧ ❪G,L❫ ⊢ ⬈*𝐒 V & ❪G,L.ⓤ[J]❫ ⊢ ⬈*𝐒 T.
/3 width=4 by csx_fwd_pair_sn, csx_fwd_bind_dx_unit, conj/ qed-.

(* Properties with restricted refinement for local environments *************)

lemma csx_lsubr_conf (G) (L1):
      ∀T. ❪G,L1❫ ⊢ ⬈*𝐒 T → ∀L2. L1 ⫃ L2 → ❪G,L2❫ ⊢ ⬈*𝐒 T.
#G #L1 #T #H
@(csx_ind … H) -T #T1 #_ #IH #L2 #HL12
@csx_intro #T2 #HT12 #HnT12
/3 width=3 by lsubr_cpx_trans/
qed-.
