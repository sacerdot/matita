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

include "basic_2A/notation/relations/prednormal_5.ma".
include "basic_2A/reduction/cnr.ma".
include "basic_2A/reduction/cpx.ma".

(* NORMAL TERMS FOR CONTEXT-SENSITIVE EXTENDED REDUCTION ********************)

definition cnx: ∀h. sd h → relation3 genv lenv term ≝
                λh,g,G,L. NF … (cpx h g G L) (eq …).

interpretation
   "normality for context-sensitive extended reduction (term)"
   'PRedNormal h g L T = (cnx h g L T).

(* Basic inversion lemmas ***************************************************)

lemma cnx_inv_sort: ∀h,g,G,L,k. ⦃G, L⦄ ⊢ ➡[h, g] 𝐍⦃⋆k⦄ → deg h g k 0.
#h #g #G #L #k #H elim (deg_total h g k)
#d @(nat_ind_plus … d) -d // #d #_ #Hkd
lapply (H (⋆(next h k)) ?) -H /2 width=2 by cpx_st/ -L -d #H
lapply (destruct_tatom_tatom_aux … H) -H #H (**) (* destruct lemma needed *)
lapply (destruct_sort_sort_aux … H) -H #H (**) (* destruct lemma needed *)
lapply (next_lt h k) <H -H #H elim (lt_refl_false … H)
qed-.

lemma cnx_inv_delta: ∀h,g,I,G,L,K,V,i. ⬇[i] L ≡ K.ⓑ{I}V → ⦃G, L⦄ ⊢ ➡[h, g] 𝐍⦃#i⦄ → ⊥.
#h #g #I #G #L #K #V #i #HLK #H
elim (lift_total V 0 (i+1)) #W #HVW
lapply (H W ?) -H [ /3 width=7 by cpx_delta/ ] -HLK #H destruct
elim (lift_inv_lref2_be … HVW) -HVW //
qed-.

lemma cnx_inv_abst: ∀h,g,a,G,L,V,T. ⦃G, L⦄ ⊢ ➡[h, g] 𝐍⦃ⓛ{a}V.T⦄ →
                    ⦃G, L⦄ ⊢ ➡[h, g] 𝐍⦃V⦄ ∧ ⦃G, L.ⓛV⦄ ⊢ ➡[h, g] 𝐍⦃T⦄.
#h #g #a #G #L #V1 #T1 #HVT1 @conj
[ #V2 #HV2 lapply (HVT1 (ⓛ{a}V2.T1) ?) -HVT1 /2 width=2 by cpx_pair_sn/ -HV2 #H destruct //
| #T2 #HT2 lapply (HVT1 (ⓛ{a}V1.T2) ?) -HVT1 /2 width=2 by cpx_bind/ -HT2 #H destruct //
]
qed-.

lemma cnx_inv_abbr: ∀h,g,G,L,V,T. ⦃G, L⦄ ⊢ ➡[h, g] 𝐍⦃-ⓓV.T⦄ →
                    ⦃G, L⦄ ⊢ ➡[h, g] 𝐍⦃V⦄ ∧ ⦃G, L.ⓓV⦄ ⊢ ➡[h, g] 𝐍⦃T⦄.
#h #g #G #L #V1 #T1 #HVT1 @conj
[ #V2 #HV2 lapply (HVT1 (-ⓓV2.T1) ?) -HVT1 /2 width=2 by cpx_pair_sn/ -HV2 #H destruct //
| #T2 #HT2 lapply (HVT1 (-ⓓV1.T2) ?) -HVT1 /2 width=2 by cpx_bind/ -HT2 #H destruct //
]
qed-.

lemma cnx_inv_zeta: ∀h,g,G,L,V,T. ⦃G, L⦄ ⊢ ➡[h, g] 𝐍⦃+ⓓV.T⦄ → ⊥.
#h #g #G #L #V #T #H elim (is_lift_dec T 0 1)
[ * #U #HTU
  lapply (H U ?) -H /2 width=3 by cpx_zeta/ #H destruct
  elim (lift_inv_pair_xy_y … HTU)
| #HT
  elim (cpr_delift G(⋆) V T (⋆.ⓓV) 0) // #T2 #T1 #HT2 #HT12
  lapply (H (+ⓓV.T2) ?) -H /5 width=1 by cpr_cpx, tpr_cpr, cpr_bind/ -HT2
  #H destruct /3 width=2 by ex_intro/
]
qed-.

lemma cnx_inv_appl: ∀h,g,G,L,V,T. ⦃G, L⦄ ⊢ ➡[h, g] 𝐍⦃ⓐV.T⦄ →
                    ∧∧ ⦃G, L⦄ ⊢ ➡[h, g] 𝐍⦃V⦄ & ⦃G, L⦄ ⊢ ➡[h, g] 𝐍⦃T⦄ & 𝐒⦃T⦄.
#h #g #G #L #V1 #T1 #HVT1 @and3_intro
[ #V2 #HV2 lapply (HVT1 (ⓐV2.T1) ?) -HVT1 /2 width=1 by cpx_pair_sn/ -HV2 #H destruct //
| #T2 #HT2 lapply (HVT1 (ⓐV1.T2) ?) -HVT1 /2 width=1 by cpx_flat/ -HT2 #H destruct //
| generalize in match HVT1; -HVT1 elim T1 -T1 * // #a * #W1 #U1 #_ #_ #H
  [ elim (lift_total V1 0 1) #V2 #HV12
    lapply (H (ⓓ{a}W1.ⓐV2.U1) ?) -H /3 width=3 by cpr_cpx, cpr_theta/ -HV12 #H destruct
  | lapply (H (ⓓ{a}ⓝW1.V1.U1) ?) -H /3 width=1 by cpr_cpx, cpr_beta/ #H destruct
  ]
]
qed-.

lemma cnx_inv_eps: ∀h,g,G,L,V,T. ⦃G, L⦄ ⊢ ➡[h, g] 𝐍⦃ⓝV.T⦄ → ⊥.
#h #g #G #L #V #T #H lapply (H T ?) -H
/2 width=4 by cpx_eps, discr_tpair_xy_y/
qed-.

(* Basic forward lemmas *****************************************************)

lemma cnx_fwd_cnr: ∀h,g,G,L,T. ⦃G, L⦄ ⊢ ➡[h, g] 𝐍⦃T⦄ → ⦃G, L⦄ ⊢ ➡ 𝐍⦃T⦄.
#h #g #G #L #T #H #U #HTU
@H /2 width=1 by cpr_cpx/ (**) (* auto fails because a δ-expansion gets in the way *)
qed-.

(* Basic properties *********************************************************)

lemma cnx_sort: ∀h,g,G,L,k. deg h g k 0 → ⦃G, L⦄ ⊢ ➡[h, g] 𝐍⦃⋆k⦄.
#h #g #G #L #k #Hk #X #H elim (cpx_inv_sort1 … H) -H // * #d #Hkd #_
lapply (deg_mono … Hkd Hk) -h -L <plus_n_Sm #H destruct
qed.

lemma cnx_sort_iter: ∀h,g,G,L,k,d. deg h g k d → ⦃G, L⦄ ⊢ ➡[h, g] 𝐍⦃⋆((next h)^d k)⦄.
#h #g #G #L #k #d #Hkd
lapply (deg_iter … d Hkd) -Hkd <minus_n_n /2 width=6 by cnx_sort/
qed.

lemma cnx_lref_free: ∀h,g,G,L,i. |L| ≤ i → ⦃G, L⦄ ⊢ ➡[h, g] 𝐍⦃#i⦄.
#h #g #G #L #i #Hi #X #H elim (cpx_inv_lref1 … H) -H // *
#I #K #V1 #V2 #HLK lapply (drop_fwd_length_lt2 … HLK) -HLK
#H elim (lt_refl_false i) /2 width=3 by lt_to_le_to_lt/
qed.

lemma cnx_lref_atom: ∀h,g,G,L,i. ⬇[i] L ≡ ⋆ → ⦃G, L⦄ ⊢ ➡[h, g] 𝐍⦃#i⦄.
#h #g #G #L #i #HL @cnx_lref_free >(drop_fwd_length … HL) -HL //
qed.

lemma cnx_abst: ∀h,g,a,G,L,W,T. ⦃G, L⦄ ⊢ ➡[h, g] 𝐍⦃W⦄ → ⦃G, L.ⓛW⦄ ⊢ ➡[h, g] 𝐍⦃T⦄ →
                ⦃G, L⦄ ⊢ ➡[h, g] 𝐍⦃ⓛ{a}W.T⦄.
#h #g #a #G #L #W #T #HW #HT #X #H
elim (cpx_inv_abst1 … H) -H #W0 #T0 #HW0 #HT0 #H destruct
<(HW … HW0) -W0 <(HT … HT0) -T0 //
qed.

lemma cnx_appl_simple: ∀h,g,G,L,V,T. ⦃G, L⦄ ⊢ ➡[h, g] 𝐍⦃V⦄ → ⦃G, L⦄ ⊢ ➡[h, g] 𝐍⦃T⦄ → 𝐒⦃T⦄ →
                       ⦃G, L⦄ ⊢ ➡[h, g] 𝐍⦃ⓐV.T⦄.
#h #g #G #L #V #T #HV #HT #HS #X #H
elim (cpx_inv_appl1_simple … H) -H // #V0 #T0 #HV0 #HT0 #H destruct
<(HV … HV0) -V0 <(HT … HT0) -T0 //
qed.

axiom cnx_dec: ∀h,g,G,L,T1. ⦃G, L⦄ ⊢ ➡[h, g] 𝐍⦃T1⦄ ∨
               ∃∃T2. ⦃G, L⦄ ⊢ T1 ➡[h, g] T2 & (T1 = T2 → ⊥).
