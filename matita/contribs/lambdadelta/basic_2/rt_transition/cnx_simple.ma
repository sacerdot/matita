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
include "basic_2/rt_transition/cnx.ma".

(* NORMAL TERMS FOR UNBOUND CONTEXT-SENSITIVE PARALLEL RT-TRANSITION ********)

(* Inversion lemmas with simple terms ***************************************)

lemma cnx_inv_appl: ∀h,G,L,V,T. ⦃G,L⦄ ⊢ ⬈[h] 𝐍⦃ⓐV.T⦄ →
                    ∧∧ ⦃G,L⦄ ⊢ ⬈[h] 𝐍⦃V⦄ & ⦃G,L⦄ ⊢ ⬈[h] 𝐍⦃T⦄ & 𝐒⦃T⦄.
#h #G #L #V1 #T1 #HVT1 @and3_intro
[ #V2 #HV2 lapply (HVT1 (ⓐV2.T1) ?) -HVT1 /2 width=1 by cpx_pair_sn/ -HV2
  #H elim (teqx_inv_pair … H) -H //
| #T2 #HT2 lapply (HVT1 (ⓐV1.T2) ?) -HVT1 /2 width=1 by cpx_flat/ -HT2
  #H elim (teqx_inv_pair … H) -H //
| generalize in match HVT1; -HVT1 elim T1 -T1 * //
  #p * #W1 #U1 #_ #_ #H
  [ elim (lifts_total V1 (𝐔❴1❵)) #V2 #HV12
    lapply (H (ⓓ{p}W1.ⓐV2.U1) ?) -H /2 width=3 by cpx_theta/ -HV12
    #H elim (teqx_inv_pair … H) -H #H destruct
  | lapply (H (ⓓ{p}ⓝW1.V1.U1) ?) -H /2 width=1 by cpx_beta/
    #H elim (teqx_inv_pair … H) -H #H destruct
  ]
]
qed-.

(* Properties with simple terms *********************************************)

lemma cnx_appl_simple: ∀h,G,L,V,T. ⦃G,L⦄ ⊢ ⬈[h] 𝐍⦃V⦄ → ⦃G,L⦄ ⊢ ⬈[h] 𝐍⦃T⦄ → 𝐒⦃T⦄ →
                       ⦃G,L⦄ ⊢ ⬈[h] 𝐍⦃ⓐV.T⦄.
#h #G #L #V #T #HV #HT #HS #X #H elim (cpx_inv_appl1_simple … H) -H //
#V0 #T0 #HV0 #HT0 #H destruct
@teqx_pair [ @HV | @HT ] // (**) (* auto fails because δ-expansion gets in the way *)
qed.
