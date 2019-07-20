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

include "basic_2/rt_computation/csx_lsubr.ma".
include "basic_2/rt_computation/csx_cpxs.ma".
include "basic_2/rt_computation/jsx_rsx.ma".

(* STRONGLY NORMALIZING REFERRED LOCAL ENV.S FOR UNBOUND RT-TRANSITION ******)

(* Advanced properties ******************************************************)

(* Note: swapping the eliminations to avoid rsx_cpx_trans: no solution found *)
(* Basic_2A1: uses: lsx_lref_be_lpxs *)
lemma rsx_pair_lpxs (h) (G):
      ∀K1,V. ⦃G,K1⦄ ⊢ ⬈*[h] 𝐒⦃V⦄ →
      ∀K2. G ⊢ ⬈*[h,V] 𝐒⦃K2⦄ → ⦃G,K1⦄ ⊢ ⬈*[h] K2 →
      ∀I. G ⊢ ⬈*[h,#0] 𝐒⦃K2.ⓑ{I}V⦄.
#h #G #K1 #V #H
@(csx_ind_cpxs … H) -V #V0 #_ #IHV0 #K2 #H
@(rsx_ind … H) -K2 #K0 #HK0 #IHK0 #HK10 #I
@rsx_intro #Y #HY #HnY
elim (lpx_inv_pair_sn … HY) -HY #K2 #V2 #HK02 #HV02 #H destruct
elim (tdeq_dec V0 V2) #HnV02 destruct [ -IHV0 -HV02 -HK0 | -IHK0 -HnY ]
[ /5 width=5 by rsx_rdeq_trans, lpxs_step_dx, rdeq_pair/
| @(IHV0 … HnV02) -IHV0 -HnV02
  [ /2 width=3 by lpxs_cpx_trans/
  | /3 width=3 by rsx_lpx_trans, rsx_cpx_trans/
  | /2 width=3 by lpxs_step_dx/
  ]
]
qed.

(* Basic_2A1: uses: lsx_lref_be *)
lemma rsx_lref_pair_drops (h) (G):
      ∀K,V. ⦃G,K⦄ ⊢ ⬈*[h] 𝐒⦃V⦄ → G ⊢ ⬈*[h,V] 𝐒⦃K⦄ →
      ∀I,i,L. ⬇*[i] L ≘ K.ⓑ{I}V → G ⊢ ⬈*[h,#i] 𝐒⦃L⦄.
#h #G #K #V #HV #HK #I #i elim i -i
[ #L #H >(drops_fwd_isid … H) -H /2 width=3 by rsx_pair_lpxs/
| #i #IH #L #H
  elim (drops_inv_bind2_isuni_next … H) -H // #J #Y #HY #H destruct
  @(rsx_lifts … (𝐔❴1❵)) /3 width=6 by drops_refl, drops_drop/ (**) (* full auto fails *)
]
qed.

(* Main properties **********************************************************)

(* Basic_2A1: uses: csx_lsx *)
theorem csx_rsx (h): ∀G,L,T. ⦃G,L⦄ ⊢ ⬈*[h] 𝐒⦃T⦄ → G ⊢ ⬈*[h,T] 𝐒⦃L⦄.
#h #G #L #T @(fqup_wf_ind_eq (Ⓕ) … G L T) -G -L -T
#Z #Y #X #IH #G #L * * //
[ #i #HG #HL #HT #H destruct
  elim (csx_inv_lref … H) -H [ |*: * ]
  [ /2 width=1 by rsx_lref_atom/
  | /2 width=3 by rsx_lref_unit/
  | /4 width=6 by rsx_lref_pair_drops, fqup_lref/
  ]
| #p #I #V #T #HG #HL #HT #H destruct
  elim (csx_fwd_bind_unit … H Void) -H /3 width=1 by rsx_bind_void/
| #I #V #T #HG #HL #HT #H destruct
  elim (csx_fwd_flat … H) -H /3 width=1 by rsx_flat/
]
qed.
