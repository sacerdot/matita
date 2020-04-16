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

include "static_2/relocation/drops_ctc.ma".
include "basic_2/rt_transition/cpx_drops.ma".
include "basic_2/rt_computation/cpxs.ma".

(* EXTENDED CONTEXT-SENSITIVE PARALLEL RT-COMPUTATION FOR TERMS *************)

(* Advanced properties ******************************************************)

lemma cpxs_delta (G) (K):
      ∀I,V1,V2. ❪G,K❫ ⊢ V1 ⬈* V2 →
      ∀W2. ⇧[1] V2 ≘ W2 → ❪G,K.ⓑ[I]V1❫ ⊢ #0 ⬈* W2.
#G #K #I #V1 #V2 #H @(cpxs_ind … H) -V2
[ /3 width=3 by cpx_cpxs, cpx_delta/
| #V #V2 #_ #HV2 #IH #W2 #HVW2
  elim (lifts_total V (𝐔❨1❩))
  /5 width=11 by cpxs_strap1, cpx_lifts_bi, drops_refl, drops_drop/
]
qed.

lemma cpxs_lref (G) (K):
      ∀I,T,i. ❪G,K❫ ⊢ #i ⬈* T →
      ∀U. ⇧[1] T ≘ U → ❪G,K.ⓘ[I]❫ ⊢ #↑i ⬈* U.
#G #K #I #T #i #H @(cpxs_ind … H) -T
[ /3 width=3 by cpx_cpxs, cpx_lref/
| #T0 #T #_ #HT2 #IH #U #HTU
  elim (lifts_total T0 (𝐔❨1❩))
  /5 width=11 by cpxs_strap1, cpx_lifts_bi, drops_refl, drops_drop/
]
qed.

(* Basic_2A1: was: cpxs_delta *)
lemma cpxs_delta_drops (G) (L):
      ∀I,K,V1,V2,i. ⇩[i] L ≘ K.ⓑ[I]V1 → ❪G,K❫ ⊢ V1 ⬈* V2 →
      ∀W2. ⇧[↑i] V2 ≘ W2 → ❪G,L❫ ⊢ #i ⬈* W2.
#G #L #I #K #V1 #V2 #i #HLK #H @(cpxs_ind … H) -V2
[ /3 width=7 by cpx_cpxs, cpx_delta_drops/
| #V #V2 #_ #HV2 #IH #W2 #HVW2
  elim (lifts_total V (𝐔❨↑i❩))
  /4 width=11 by cpxs_strap1, cpx_lifts_bi, drops_isuni_fwd_drop2/
]
qed.

(* Advanced inversion lemmas ************************************************)

lemma cpxs_inv_zero1 (G) (L):
      ∀T2. ❪G,L❫ ⊢ #0 ⬈* T2 →
      ∨∨ T2 = #0
       | ∃∃I,K,V1,V2. ❪G,K❫ ⊢ V1 ⬈* V2 & ⇧[1] V2 ≘ T2 & L = K.ⓑ[I]V1.
#G #L #T2 #H @(cpxs_ind … H) -T2 /2 width=1 by or_introl/
#T #T2 #_ #HT2 *
[ #H destruct
  elim (cpx_inv_zero1 … HT2) -HT2 /2 width=1 by or_introl/
  * /4 width=7 by cpx_cpxs, ex3_4_intro, or_intror/
| * #I #K #V1 #T1 #HVT1 #HT1 #H destruct
  elim (cpx_inv_lifts_sn … HT2 (Ⓣ) … K … HT1) -T
  /4 width=7 by cpxs_strap1, drops_refl, drops_drop, ex3_4_intro, or_intror/
]
qed-.

lemma cpxs_inv_lref1 (G) (L):
      ∀T2,i. ❪G,L❫ ⊢ #↑i ⬈* T2 →
      ∨∨ T2 = #(↑i)
       | ∃∃I,K,T. ❪G,K❫ ⊢ #i ⬈* T & ⇧[1] T ≘ T2 & L = K.ⓘ[I].
#G #L #T2 #i #H @(cpxs_ind … H) -T2 /2 width=1 by or_introl/
#T #T2 #_ #HT2 *
[ #H destruct
  elim (cpx_inv_lref1 … HT2) -HT2 /2 width=1 by or_introl/
  * /4 width=6 by cpx_cpxs, ex3_3_intro, or_intror/
| * #I #K #T1 #Hi #HT1 #H destruct
  elim (cpx_inv_lifts_sn … HT2 (Ⓣ) … K … HT1) -T
  /4 width=6 by cpxs_strap1, drops_refl, drops_drop, ex3_3_intro, or_intror/
]
qed-.

(* Basic_2A1: was: cpxs_inv_lref1 *)
lemma cpxs_inv_lref1_drops (G) (L):
      ∀T2,i. ❪G,L❫ ⊢ #i ⬈* T2 →
      ∨∨ T2 = #i
       | ∃∃I,K,V1,T1. ⇩[i] L ≘ K.ⓑ[I]V1 & ❪G,K❫ ⊢ V1 ⬈* T1 & ⇧[↑i] T1 ≘ T2.
#G #L #T2 #i #H @(cpxs_ind … H) -T2 /2 width=1 by or_introl/
#T #T2 #_ #HT2 *
[ #H destruct
  elim (cpx_inv_lref1_drops … HT2) -HT2 /2 width=1 by or_introl/
  * /4 width=7 by cpx_cpxs, ex3_4_intro, or_intror/
| * #I #K #V1 #T1 #HLK #HVT1 #HT1
  lapply (drops_isuni_fwd_drop2 … HLK) // #H0LK
  elim (cpx_inv_lifts_sn … HT2 … H0LK … HT1) -H0LK -T
  /4 width=7 by cpxs_strap1, ex3_4_intro, or_intror/
]
qed-.

(* Properties with generic relocation ***************************************)

(* Basic_2A1: includes: cpxs_lift *)
lemma cpxs_lifts_sn (G):
      d_liftable2_sn … lifts (cpxs G).
/3 width=10 by cpx_lifts_sn, cpxs_strap1, d2_liftable_sn_CTC/ qed-.

lemma cpxs_lifts_bi (G):
      d_liftable2_bi … lifts (cpxs G).
/3 width=12 by cpxs_lifts_sn, d_liftable2_sn_bi, lifts_mono/ qed-.

(* Inversion lemmas with generic relocation *********************************)

(* Basic_2A1: includes: cpxs_inv_lift1 *)
lemma cpxs_inv_lifts_sn (G):
      d_deliftable2_sn … lifts (cpxs G).
/3 width=6 by d2_deliftable_sn_CTC, cpx_inv_lifts_sn/ qed-.

lemma cpxs_inv_lifts_bi (G):
      d_deliftable2_bi … lifts (cpxs G).
/3 width=12 by cpxs_inv_lifts_sn, d_deliftable2_sn_bi, lifts_inj/ qed-.
