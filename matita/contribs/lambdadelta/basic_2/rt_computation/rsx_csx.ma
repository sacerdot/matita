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

(* Forward lemmas with strongly rt-normalizing terms ************************)

fact rsx_fwd_lref_pair_csx_aux (h) (G):
     ∀L. G ⊢ ⬈*[h,#0] 𝐒⦃L⦄ →
     ∀I,K,V. L = K.ⓑ{I}V → ⦃G,K⦄ ⊢ ⬈*[h] 𝐒⦃V⦄.
#h #G #L #H
@(rsx_ind … H) -L #L #_ #IH #I #K #V1 #H destruct
@csx_intro #V2 #HV12 #HnV12
@(IH … I) -IH [1,4: // | -HnV12 | -G #H ]
[ /2 width=1 by lpx_pair/
| elim (reqx_inv_zero_pair_sn … H) -H #Y #X #_ #H1 #H2 destruct -I
  /2 width=1 by/
]
qed-.

lemma rsx_fwd_lref_pair_csx (h) (G):
      ∀I,K,V. G ⊢ ⬈*[h,#0] 𝐒⦃K.ⓑ{I}V⦄ → ⦃G,K⦄ ⊢ ⬈*[h] 𝐒⦃V⦄.
/2 width=4 by rsx_fwd_lref_pair_csx_aux/ qed-.

lemma rsx_fwd_lref_pair_csx_drops (h) (G):
      ∀I,K,V,i,L. ⇩*[i] L ≘ K.ⓑ{I}V → G ⊢ ⬈*[h,#i] 𝐒⦃L⦄ → ⦃G,K⦄ ⊢ ⬈*[h] 𝐒⦃V⦄.
#h #G #I #K #V #i elim i -i
[ #L #H >(drops_fwd_isid … H) -H
  /2 width=2 by rsx_fwd_lref_pair_csx/
| #i #IH #L #H1 #H2
  elim (drops_inv_bind2_isuni_next … H1) -H1 // #J #Y #HY #H destruct
  lapply (rsx_inv_lifts … H2 … (𝐔❴1❵) ?????) -H2
  /3 width=6 by drops_refl, drops_drop/
]
qed-.

(* Inversion lemmas with strongly rt-normalizing terms **********************)

lemma rsx_inv_lref_pair (h) (G):
      ∀I,K,V. G ⊢ ⬈*[h,#0] 𝐒⦃K.ⓑ{I}V⦄ →
      ∧∧ ⦃G,K⦄ ⊢ ⬈*[h] 𝐒⦃V⦄  & G ⊢ ⬈*[h,V] 𝐒⦃K⦄.
/3 width=2 by rsx_fwd_lref_pair_csx, rsx_fwd_pair, conj/ qed-.

lemma rsx_inv_lref_pair_drops (h) (G):
      ∀I,K,V,i,L. ⇩*[i] L ≘ K.ⓑ{I}V → G ⊢ ⬈*[h,#i] 𝐒⦃L⦄ →
      ∧∧ ⦃G,K⦄ ⊢ ⬈*[h] 𝐒⦃V⦄ & G ⊢ ⬈*[h,V] 𝐒⦃K⦄.
/3 width=5 by rsx_fwd_lref_pair_csx_drops, rsx_fwd_lref_pair_drops, conj/ qed-.

lemma rsx_inv_lref_drops (h) (G):
      ∀L,i. G ⊢ ⬈*[h,#i] 𝐒⦃L⦄ →
      ∨∨ ⇩*[Ⓕ,𝐔❴i❵] L ≘ ⋆
       | ∃∃I,K. ⇩*[i] L ≘ K.ⓤ{I}
       | ∃∃I,K,V. ⇩*[i] L ≘ K.ⓑ{I}V & ⦃G,K⦄ ⊢ ⬈*[h] 𝐒⦃V⦄ & G ⊢ ⬈*[h,V] 𝐒⦃K⦄.
#h #G #L #i #H elim (drops_F_uni L i)
[ /2 width=1 by or3_intro0/
| * * /4 width=10 by rsx_fwd_lref_pair_csx_drops, rsx_fwd_lref_pair_drops, ex3_3_intro, ex1_2_intro, or3_intro2, or3_intro1/
]
qed-.

(* Properties with strongly rt-normalizing terms ****************************)

(* Note: swapping the eliminations to avoid rsx_cpx_trans: no solution found *)
(* Basic_2A1: uses: lsx_lref_be_lpxs *)
lemma rsx_lref_pair_lpxs (h) (G):
      ∀K1,V. ⦃G,K1⦄ ⊢ ⬈*[h] 𝐒⦃V⦄ →
      ∀K2. G ⊢ ⬈*[h,V] 𝐒⦃K2⦄ → ⦃G,K1⦄ ⊢ ⬈*[h] K2 →
      ∀I. G ⊢ ⬈*[h,#0] 𝐒⦃K2.ⓑ{I}V⦄.
#h #G #K1 #V #H
@(csx_ind_cpxs … H) -V #V0 #_ #IHV0 #K2 #H
@(rsx_ind … H) -K2 #K0 #HK0 #IHK0 #HK10 #I
@rsx_intro #Y #HY #HnY
elim (lpx_inv_pair_sn … HY) -HY #K2 #V2 #HK02 #HV02 #H destruct
elim (teqx_dec V0 V2) #HnV02 destruct [ -IHV0 -HV02 -HK0 | -IHK0 -HnY ]
[ /5 width=5 by rsx_reqx_trans, lpxs_step_dx, reqx_pair/
| @(IHV0 … HnV02) -IHV0 -HnV02
  [ /2 width=3 by lpxs_cpx_trans/
  | /3 width=3 by rsx_lpx_trans, rsx_cpx_trans/
  | /2 width=3 by lpxs_step_dx/
  ]
]
qed.

lemma rsx_lref_pair (h) (G):
      ∀K,V. ⦃G,K⦄ ⊢ ⬈*[h] 𝐒⦃V⦄ → G ⊢ ⬈*[h,V] 𝐒⦃K⦄ → ∀I. G ⊢ ⬈*[h,#0] 𝐒⦃K.ⓑ{I}V⦄.
/2 width=3 by rsx_lref_pair_lpxs/ qed.

(* Basic_2A1: uses: lsx_lref_be *)
lemma rsx_lref_pair_drops (h) (G):
      ∀K,V. ⦃G,K⦄ ⊢ ⬈*[h] 𝐒⦃V⦄ → G ⊢ ⬈*[h,V] 𝐒⦃K⦄ →
      ∀I,i,L. ⇩*[i] L ≘ K.ⓑ{I}V → G ⊢ ⬈*[h,#i] 𝐒⦃L⦄.
#h #G #K #V #HV #HK #I #i elim i -i
[ #L #H >(drops_fwd_isid … H) -H /2 width=1 by rsx_lref_pair/
| #i #IH #L #H
  elim (drops_inv_bind2_isuni_next … H) -H // #J #Y #HY #H destruct
  @(rsx_lifts … (𝐔❴1❵)) /3 width=6 by drops_refl, drops_drop/ (**) (* full auto fails *)
]
qed.

(* Main properties with strongly rt-normalizing terms ***********************)

(* Basic_2A1: uses: csx_lsx *)
theorem csx_rsx (h) (G): ∀L,T. ⦃G,L⦄ ⊢ ⬈*[h] 𝐒⦃T⦄ → G ⊢ ⬈*[h,T] 𝐒⦃L⦄.
#h #G #L #T @(fqup_wf_ind_eq (Ⓣ) … G L T) -G -L -T
#Z #Y #X #IH #G #L * *
[ //
| #i #HG #HL #HT #H destruct
  elim (csx_inv_lref_drops … H) -H [ |*: * ]
  [ /2 width=1 by rsx_lref_atom_drops/
  | /2 width=3 by rsx_lref_unit_drops/
  | /4 width=6 by rsx_lref_pair_drops, fqup_lref/
  ]
| //
| #p #I #V #T #HG #HL #HT #H destruct
  elim (csx_fwd_bind … H) -H /3 width=1 by rsx_bind/
| #I #V #T #HG #HL #HT #H destruct
  elim (csx_fwd_flat … H) -H /3 width=1 by rsx_flat/
]
qed.
