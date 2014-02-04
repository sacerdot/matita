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

include "basic_2/relocation/cny_lift.ma".
include "basic_2/substitution/fqup.ma".
include "basic_2/substitution/cpys_lift.ma".
include "basic_2/substitution/cpye.ma".

(* EVALUATION FOR CONTEXT-SENSITIVE EXTENDED SUBSTITUTION ON TERMS **********)

(* Advanced properties ******************************************************)

lemma cpye_subst: ∀I,G,L,K,V1,V2,W2,i,d,e. d ≤ yinj i → i < d + e →
                  ⇩[i] L ≡ K.ⓑ{I}V1 → ⦃G, K⦄ ⊢ V1 ▶*[O, ⫰(d+e-i)] 𝐍⦃V2⦄ →
                  ⇧[O, i+1] V2 ≡ W2 → ⦃G, L⦄ ⊢ #i ▶*[d, e] 𝐍⦃W2⦄.
#I #G #L #K #V1 #V2 #W2 #i #d #e #Hdi #Hide #HLK *
/4 width=13 by cpys_subst, cny_subst_aux, ldrop_fwd_drop2, conj/
qed.

lemma cpys_total: ∀G,L,T1,d,e. ∃T2. ⦃G, L⦄ ⊢ T1 ▶*[d, e] 𝐍⦃T2⦄.
#G #L #T1 @(fqup_wf_ind_eq … G L T1) -G -L -T1
#Z #Y #X #IH #G #L * *
[ #k #HG #HL #HT #d #e destruct -IH /2 width=2 by ex_intro/
| #i #HG #HL #HT #d #e destruct
  elim (ylt_split i d) /3 width=2 by cpye_skip, ex_intro/
  elim (ylt_split i (d+e)) /3 width=2 by cpye_top, ex_intro/
  elim (lt_or_ge i (|L|)) /3 width=2 by cpye_free, ex_intro/
  #Hi #Hide #Hdi elim (ldrop_O1_lt L i) // -Hi
  #I #K #V1 #HLK elim (IH G K V1 … 0 (⫰(d+e-i))) -IH /2 width=2 by fqup_lref/
  #V2 elim (lift_total V2 0 (i+1)) /3 width=8 by ex_intro, cpye_subst/
| #p #HG #HL #HT #d #e destruct -IH /2 width=2 by ex_intro/
| #a #I #V1 #T1 #HG #HL #HT #d #e destruct
  elim (IH G L V1 … d e) // elim (IH G (L.ⓑ{I}V1) T1 … (⫯d) e) //
  /3 width=2 by cpye_bind, ex_intro/
| #I #V1 #T1 #HG #HL #HT #d #e destruct
  elim (IH G L V1 … d e) // elim (IH G L T1 … d e) //
  /3 width=2 by cpye_flat, ex_intro/
]
qed-.

(* Advanced inversion lemmas ************************************************)

lemma cpye_inv_lref1: ∀G,L,T2,d,e,i. ⦃G, L⦄ ⊢ #i ▶*[d, e] 𝐍⦃T2⦄ →
                      ∨∨ |L| ≤ i ∧ T2 = #i
                       | d + e ≤ yinj i ∧ T2 = #i
                       | yinj i < d ∧ T2 = #i
                       | ∃∃I,K,V1,V2. d ≤ yinj i & yinj i < d + e &
                                      ⇩[i] L ≡ K.ⓑ{I}V1 &
                                      ⦃G, K⦄ ⊢ V1 ▶*[yinj 0, ⫰(d+e-yinj i)]  𝐍⦃V2⦄ &
                                      ⇧[O, i+1] V2 ≡ T2.
#G #L #T2 #i #d #e * #H1 #H2 elim (cpys_inv_lref1 … H1) -H1
[ #H destruct elim (cny_inv_lref … H2) -H2
  /3 width=1 by or4_intro0, or4_intro1, or4_intro2, conj/
| * #I #K #V1 #V2 #Hdi #Hide #HLK #HV12 #HVT2
    @or4_intro3 @(ex5_4_intro … HLK … HVT2) (**) (* explicit constructor *)
    /4 width=13 by cny_inv_subst_aux, ldrop_fwd_drop2, conj/
]
qed-.

lemma cpye_inv_lref1_free: ∀G,L,T2,d,e,i. ⦃G, L⦄ ⊢ #i ▶*[d, e] 𝐍⦃T2⦄ →
                           (∨∨ |L| ≤ i | d + e ≤ yinj i | yinj i < d) → T2 = #i.
#G #L #T2 #d #e #i #H * elim (cpye_inv_lref1 … H) -H * //
#I #K #V1 #V2 #Hdi #Hide #HLK #_ #_ #H
[ elim (lt_refl_false i) -d
  @(lt_to_le_to_lt … H) -H /2 width=5 by ldrop_fwd_length_lt2/ (**) (* full auto slow: 19s *)
]
elim (ylt_yle_false … H) //
qed-.

lemma cpye_inv_lref1_subst: ∀G,L,T2,d,e,i. ⦃G, L⦄ ⊢ #i ▶*[d, e] 𝐍⦃T2⦄ →
                            ∀I,K,V1,V2. d ≤ yinj i → yinj i < d + e →
                            ⇩[i] L ≡ K.ⓑ{I}V1 → ⇧[O, i+1] V2 ≡ T2 →
                            ⦃G, K⦄ ⊢ V1 ▶*[yinj 0, ⫰(d+e-yinj i)]  𝐍⦃V2⦄.
#G #L #T2 #d #e #i #H #I #K #V1 #V2 #Hdi #Hide #HLK #HVT2 elim (cpye_inv_lref1 … H) -H *
[ #H elim (lt_refl_false i) -V2 -T2 -d
  @(lt_to_le_to_lt … H) -H /2 width=5 by ldrop_fwd_length_lt2/
|2,3: #H elim (ylt_yle_false … H) //
| #Z #Y #X1 #X2 #_ #_ #HLY #HX12 #HXT2
  lapply (ldrop_mono … HLY … HLK) -HLY -HLK #H destruct
  lapply (lift_inj … HXT2 … HVT2) -HXT2 -HVT2 #H destruct //
]
qed-.
