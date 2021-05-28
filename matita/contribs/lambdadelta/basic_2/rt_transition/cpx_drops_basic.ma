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

include "static_2/relocation/lifts_basic.ma".
include "basic_2/rt_transition/cpx_drops.ma".

(* EXTENDED CONTEXT-SENSITIVE PARALLEL RT-TRANSITION FOR TERMS **************)

(* Properties with basic relocation *****************************************)

lemma cpx_subst (G) (L) (U1) (i):
      ∀I,K,V. ⇩[i] L ≘ K.ⓑ[I]V →
      ∃∃U2,T2. ❪G,L❫ ⊢ U1 ⬈ U2 & ⇧[i,1] T2 ≘ U2.
#G #L #U1 @(fqup_wf_ind_eq (Ⓣ) … G L U1) -G -L -U1
#G0 #L0 #U0 #IH #G #L * *
[ #s #HG #HL #HT #i #I #K #V #_ destruct -IH
  /2 width=4 by lifts_sort, ex2_2_intro/
| #j #HG #HL #HT #i #I #K #V #HLK destruct -IH
  elim (lt_or_eq_or_gt i j) #Hij
  [ /3 width=4 by lifts_lref_ge_minus, cpx_refl, ex2_2_intro/
  | elim (lifts_total V (𝐔❨↑i❩)) #U2 #HU2
    elim (lifts_split_trans … HU2 (𝐔❨i❩) (𝐛❨i,1❩)) [2: @(after_basic_rc i 0) ]
    /3 width=7 by cpx_delta_drops, ex2_2_intro/
  | /3 width=4 by lifts_lref_lt, cpx_refl, ex2_2_intro/
  ]
| #l #HG #HL #HT #i #I #K #V #_ destruct -IH
  /2 width=4 by lifts_gref, ex2_2_intro/
| #p #J #W1 #U1 #HG #HL #HT #i #I #K #V #HLK destruct
  elim (IH G L W1 … HLK) [| // ] #W2 #V2 #HW12 #HVW2
  elim (IH G (L.ⓑ[J]W1) U1 … (↑i)) [|*: /3 width=4 by drops_drop/ ] #U2 #T2 #HU12 #HTU2
  /3 width=9 by cpx_bind, lifts_bind, ex2_2_intro/
| #J #W1 #U1 #HG #HL #HT #i #I #K #V #HLK destruct
  elim (IH G L W1 … HLK) [| // ] #W2 #V2 #HW12 #HVW2
  elim (IH G L U1 … HLK) [| // ] #U2 #T2 #HU12 #HTU2
  /3 width=8 by cpx_flat, lifts_flat, ex2_2_intro/
]
qed-.
