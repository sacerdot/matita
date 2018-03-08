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

include "basic_2/rt_computation/lpxs_lpx.ma".
include "basic_2/rt_computation/lpxs_cpxs.ma".
include "basic_2/rt_computation/csx_cpxs.ma".
include "basic_2/rt_computation/csx_lsubr.ma".
include "basic_2/rt_computation/lfsx_lpx.ma".
include "basic_2/rt_computation/lsubsx_lfsx.ma".

(* STRONGLY NORMALIZING LOCAL ENV.S FOR UNCOUNTED PARALLEL RT-TRANSITION ****)

(* Advanced properties ******************************************************)

(* Basic_2A1: uses: lsx_lref_be_lpxs *)
lemma lfsx_pair_lpxs: ∀h,o,G,K1,V. ⦃G, K1⦄ ⊢ ⬈*[h, o] 𝐒⦃V⦄ →
                      ∀K2. G ⊢ ⬈*[h, o, V] 𝐒⦃K2⦄ → ⦃G, K1⦄ ⊢ ⬈*[h] K2 →
                      ∀I. G ⊢ ⬈*[h, o, #0] 𝐒⦃K2.ⓑ{I}V⦄.
#h #o #G #K1 #V #H
@(csx_ind_cpxs … H) -V #V0 #_ #IHV0 #K2 #H
@(lfsx_ind_lpx … H) -K2 #K0 #HK0 #IHK0 #HK10 #I
@lfsx_intro_lpx #Y #HY #HnY
elim (lpx_inv_pair_sn … HY) -HY #K2 #V2 #HK02 #HV02 #H destruct
elim (tdeq_dec h o V0 V2) #HnV02 destruct [ -IHV0 -HV02 -HK0 | -IHK0 -HnY ]
[ /5 width=5 by lfsx_lfdeq_trans, lpxs_step_dx, lfdeq_pair/
| @(IHV0 … HnV02) -IHV0 -HnV02
  [ /2 width=3 by lpxs_cpx_trans/
  | /3 width=3 by lfsx_lpx_trans, lfsx_cpx_trans/
  | /2 width=3 by lpxs_step_dx/
  ]
]
qed.

(* Basic_2A1: uses: lsx_lref_be *)
lemma lfsx_lref_pair_drops: ∀h,o,G,K,V. ⦃G, K⦄ ⊢ ⬈*[h, o] 𝐒⦃V⦄ → G ⊢ ⬈*[h, o, V] 𝐒⦃K⦄ →
                            ∀I,i,L. ⬇*[i] L ≡ K.ⓑ{I}V → G ⊢ ⬈*[h, o, #i] 𝐒⦃L⦄.
#h #o #G #K #V #HV #HK #I #i elim i -i
[ #L #H >(drops_fwd_isid … H) -H /2 width=3 by lfsx_pair_lpxs/
| #i #IH #L #H
  elim (drops_inv_bind2_isuni_next … H) -H // #J #Y #HY #H destruct
  @(lfsx_lifts … (𝐔❴1❵)) /3 width=6 by drops_refl, drops_drop/ (**) (* full auto fails *)
]
qed.

(* Main properties **********************************************************)

(* Basic_2A1: uses: csx_lsx *)
theorem csx_lfsx: ∀h,o,G,L,T. ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃T⦄ → G ⊢ ⬈*[h, o, T] 𝐒⦃L⦄.
#h #o #G #L #T @(fqup_wf_ind_eq (Ⓕ) … G L T) -G -L -T
#Z #Y #X #IH #G #L * * //
[ #i #HG #HL #HT #H destruct
  elim (csx_inv_lref … H) -H [ |*: * ]
  [ /2 width=1 by lfsx_lref_atom/
  | /2 width=3 by lfsx_lref_unit/
  | /4 width=6 by lfsx_lref_pair_drops, fqup_lref/
  ]
| #p #I #V #T #HG #HL #HT #H destruct
  elim (csx_fwd_bind_unit … H Void) -H /3 width=1 by lfsx_bind_void/
| #I #V #T #HG #HL #HT #H destruct
  elim (csx_fwd_flat … H) -H /3 width=1 by lfsx_flat/
]
qed.
