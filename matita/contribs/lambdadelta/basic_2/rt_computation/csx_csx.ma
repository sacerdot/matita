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

include "basic_2/rt_transition/lpx_reqx.ma".
include "basic_2/rt_computation/csx_drops.ma".

(* STRONGLY NORMALIZING TERMS FOR EXTENDED PARALLEL RT-TRANSITION ***********)

(* Advanced properties ******************************************************)

lemma csx_teqx_trans (G) (L):
      ∀T1. ❪G,L❫ ⊢ ⬈*𝐒 T1 →
      ∀T2. T1 ≛ T2 → ❪G,L❫ ⊢ ⬈*𝐒 T2.
#G #L #T1 #H @(csx_ind … H) -T1 #T #_ #IH #T2 #HT2
@csx_intro #T1 #HT21 #HnT21 elim (teqx_cpx_trans … HT2 … HT21) -HT21
/4 width=5 by teqx_repl/
qed-.

lemma csx_cpx_trans (G) (L):
      ∀T1. ❪G,L❫ ⊢ ⬈*𝐒 T1 →
      ∀T2. ❪G,L❫ ⊢ T1 ⬈ T2 → ❪G,L❫ ⊢ ⬈*𝐒 T2.
#G #L #T1 #H @(csx_ind … H) -T1 #T1 #HT1 #IHT1 #T2 #HLT12
elim (teqx_dec T1 T2) /3 width=4 by csx_teqx_trans/
qed-.

(* Basic_1: was just: sn3_cast *)
lemma csx_cast (G) (L):
      ∀W. ❪G,L❫ ⊢ ⬈*𝐒 W →
      ∀T. ❪G,L❫ ⊢ ⬈*𝐒 T → ❪G,L❫ ⊢ ⬈*𝐒 ⓝW.T.
#G #L #W #HW @(csx_ind … HW) -W
#W #HW #IHW #T #HT @(csx_ind … HT) -T
#T #HT #IHT @csx_intro
#X #H1 #H2 elim (cpx_inv_cast1 … H1) -H1
[ * #W0 #T0 #HLW0 #HLT0 #H destruct
  elim (tneqx_inv_pair … H2) -H2
  [ -W -T #H elim H -H //
  | -HW -IHT /3 width=3 by csx_cpx_trans/
  | -HW -HT -IHW /4 width=3 by csx_cpx_trans, cpx_pair_sn/
  ]
|*: /3 width=3 by csx_cpx_trans/
]
qed.

(* Basic_1: was just: sn3_abbr *)
(* Basic_2A1: was: csx_lref_bind *)
lemma csx_lref_pair_drops (G) (L):
      ∀I,K,V,i. ⇩[i] L ≘ K.ⓑ[I]V →
      ❪G,K❫ ⊢ ⬈*𝐒 V → ❪G,L❫ ⊢ ⬈*𝐒 #i.
#G #L #I #K #V #i #HLK #HV
@csx_intro #X #H #Hi elim (cpx_inv_lref1_drops … H) -H
[ #H destruct elim Hi //
| -Hi * #I0 #K0 #V0 #V1 #HLK0 #HV01 #HV1
  lapply (drops_mono … HLK0 … HLK) -HLK #H destruct
  /3 width=8 by csx_lifts, csx_cpx_trans, drops_isuni_fwd_drop2/
]
qed.

(* Advanced inversion lemmas ************************************************)

(* Basic_1: was: sn3_gen_def *)
(* Basic_2A1: was: csx_inv_lref_bind *)
lemma csx_inv_lref_pair_drops (G) (L):
      ∀I,K,V,i. ⇩[i] L ≘ K.ⓑ[I]V →
      ❪G,L❫ ⊢ ⬈*𝐒 #i → ❪G,K❫ ⊢ ⬈*𝐒 V.
#G #L #I #K #V #i #HLK #Hi
elim (lifts_total V (𝐔❨↑i❩))
/4 width=9 by csx_inv_lifts, csx_cpx_trans, cpx_delta_drops, drops_isuni_fwd_drop2/
qed-.

lemma csx_inv_lref_drops (G) (L):
      ∀i. ❪G,L❫ ⊢ ⬈*𝐒 #i →
      ∨∨ ⇩*[Ⓕ,𝐔❨i❩] L ≘ ⋆
       | ∃∃I,K. ⇩[i] L ≘ K.ⓤ[I]
       | ∃∃I,K,V. ⇩[i] L ≘ K.ⓑ[I]V & ❪G,K❫ ⊢ ⬈*𝐒 V.
#G #L #i #H elim (drops_F_uni L i) /2 width=1 by or3_intro0/
* * /4 width=9 by csx_inv_lref_pair_drops, ex2_3_intro, ex1_2_intro, or3_intro2, or3_intro1/
qed-.
