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
/4 width=13 by cpys_subst, cny_lift_subst, ldrop_fwd_drop2, conj/
qed.

lemma cpye_total: ∀G,L,T1,d,e. ∃T2. ⦃G, L⦄ ⊢ T1 ▶*[d, e] 𝐍⦃T2⦄.
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
    /4 width=13 by cny_inv_lift_subst, ldrop_fwd_drop2, conj/
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

lemma cpye_inv_lref1_lget: ∀G,L,T2,d,e,i. ⦃G, L⦄ ⊢ #i ▶*[d, e] 𝐍⦃T2⦄ →
                           ∀I,K,V1. ⇩[i] L ≡ K.ⓑ{I}V1 →
                           ∨∨ d + e ≤ yinj i ∧ T2 = #i
                            | yinj i < d ∧ T2 = #i
                            | ∃∃V2. d ≤ yinj i & yinj i < d + e &
                                    ⦃G, K⦄ ⊢ V1 ▶*[yinj 0, ⫰(d+e-yinj i)]  𝐍⦃V2⦄ &
                                    ⇧[O, i+1] V2 ≡ T2.
#G #L #T2 #d #e #i #H #I #K #V1 #HLK elim (cpye_inv_lref1 … H) -H *
[ #H elim (lt_refl_false i) -T2 -d
  @(lt_to_le_to_lt … H) -H /2 width=5 by ldrop_fwd_length_lt2/
| /3 width=1 by or3_intro0, conj/
| /3 width=1 by or3_intro1, conj/
| #Z #Y #X1 #X2 #Hdi #Hide #HLY #HX12 #HXT2
  lapply (ldrop_mono … HLY … HLK) -HLY -HLK #H destruct
  /3 width=3 by or3_intro2, ex4_intro/
]
qed-.

lemma cpye_inv_lref1_subst_ex: ∀G,L,T2,d,e,i. ⦃G, L⦄ ⊢ #i ▶*[d, e] 𝐍⦃T2⦄ →
                               ∀I,K,V1. d ≤ yinj i → yinj i < d + e →
                               ⇩[i] L ≡ K.ⓑ{I}V1 →
                               ∃∃V2. ⦃G, K⦄ ⊢ V1 ▶*[yinj 0, ⫰(d+e-yinj i)]  𝐍⦃V2⦄ &
                                     ⇧[O, i+1] V2 ≡ T2.
#G #L #T2 #d #e #i #H #I #K #V1 #Hdi #Hide #HLK
elim (cpye_inv_lref1_lget … H … HLK) -H * /2 width=3 by ex2_intro/
#H elim (ylt_yle_false … H) //
qed-.

lemma cpye_inv_lref1_subst: ∀G,L,T2,d,e,i. ⦃G, L⦄ ⊢ #i ▶*[d, e] 𝐍⦃T2⦄ →
                            ∀I,K,V1,V2. d ≤ yinj i → yinj i < d + e →
                            ⇩[i] L ≡ K.ⓑ{I}V1 → ⇧[O, i+1] V2 ≡ T2 →
                            ⦃G, K⦄ ⊢ V1 ▶*[yinj 0, ⫰(d+e-yinj i)]  𝐍⦃V2⦄.
#G #L #T2 #d #e #i #H #I #K #V1 #V2 #Hdi #Hide #HLK #HVT2
elim (cpye_inv_lref1_subst_ex … H … HLK) -H -HLK //
#X2 #H0 #HXT2 lapply (lift_inj … HXT2 … HVT2) -HXT2 -HVT2 #H destruct //
qed-.

(* Inversion lemmas on relocation *******************************************)

lemma cpye_inv_lift1_le: ∀G,L,U1,U2,dt,et. ⦃G, L⦄ ⊢ U1 ▶*[dt, et] 𝐍⦃U2⦄ →
                         ∀K,s,d,e. ⇩[s, d, e] L ≡ K → ∀T1. ⇧[d, e] T1 ≡ U1 →
                         dt + et ≤ d →
                         ∃∃T2. ⦃G, K⦄ ⊢ T1 ▶*[dt, et] 𝐍⦃T2⦄ & ⇧[d, e] T2 ≡ U2.
#G #L #U1 #U2 #dt #et * #HU12 #HU2 #K #s #d #e #HLK #T1 #HTU1 #Hdetd
elim (cpys_inv_lift1_le … HU12 … HLK … HTU1) -U1 // #T2 #HT12 #HTU2
lapply (cny_inv_lift_le … HU2 … HLK … HTU2 ?) -L
/3 width=3 by ex2_intro, conj/
qed-.

lemma cpye_inv_lift1_be: ∀G,L,U1,U2,dt,et. ⦃G, L⦄ ⊢ U1 ▶*[dt, et] 𝐍⦃U2⦄ →
                         ∀K,s,d,e. ⇩[s, d, e] L ≡ K → ∀T1. ⇧[d, e] T1 ≡ U1 →
                         dt ≤ d → yinj d + e ≤ dt + et →
                         ∃∃T2. ⦃G, K⦄ ⊢ T1 ▶*[dt, et - e] 𝐍⦃T2⦄ & ⇧[d, e] T2 ≡ U2.
#G #L #U1 #U2 #dt #et * #HU12 #HU2 #K #s #d #e #HLK #T1 #HTU1 #Hdtd #Hdedet
elim (cpys_inv_lift1_be … HU12 … HLK … HTU1) -U1 // #T2 #HT12 #HTU2
lapply (cny_inv_lift_be … HU2 … HLK … HTU2 ? ?) -L
/3 width=3 by ex2_intro, conj/
qed-.

lemma cpye_inv_lift1_ge: ∀G,L,U1,U2,dt,et. ⦃G, L⦄ ⊢ U1 ▶*[dt, et] 𝐍⦃U2⦄ →
                         ∀K,s,d,e. ⇩[s, d, e] L ≡ K → ∀T1. ⇧[d, e] T1 ≡ U1 →
                         yinj d + e ≤ dt →
                         ∃∃T2. ⦃G, K⦄ ⊢ T1 ▶*[dt - e, et] 𝐍⦃T2⦄ & ⇧[d, e] T2 ≡ U2.
#G #L #U1 #U2 #dt #et * #HU12 #HU2 #K #s #d #e #HLK #T1 #HTU1 #Hdedt
elim (cpys_inv_lift1_ge … HU12 … HLK … HTU1) -U1 // #T2 #HT12 #HTU2
lapply (cny_inv_lift_ge … HU2 … HLK … HTU2 ?) -L
/3 width=3 by ex2_intro, conj/
qed-.

lemma cpye_inv_lift1_ge_up: ∀G,L,U1,U2,dt,et. ⦃G, L⦄ ⊢ U1 ▶*[dt, et] 𝐍⦃U2⦄ →
                            ∀K,s,d,e. ⇩[s, d, e] L ≡ K → ∀T1. ⇧[d, e] T1 ≡ U1 →
                            d ≤ dt → dt ≤ yinj d + e → yinj d + e ≤ dt + et →
                            ∃∃T2. ⦃G, K⦄ ⊢ T1 ▶*[d, dt + et - (yinj d + e)] 𝐍⦃T2⦄ &
                                 ⇧[d, e] T2 ≡ U2.
#G #L #U1 #U2 #dt #et * #HU12 #HU2 #K #s #d #e #HLK #T1 #HTU1 #Hddt #Hdtde #Hdedet
elim (cpys_inv_lift1_ge_up … HU12 … HLK … HTU1) -U1 // #T2 #HT12 #HTU2
lapply (cny_inv_lift_ge_up … HU2 … HLK … HTU2 ? ? ?) -L
/3 width=3 by ex2_intro, conj/
qed-.

lemma cpye_inv_lift1_subst: ∀G,L,W1,W2,d,e. ⦃G, L⦄ ⊢ W1 ▶*[d, e] 𝐍⦃W2⦄ →
                            ∀K,V1,i. ⇩[i+1] L ≡ K → ⇧[O, i+1] V1 ≡ W1 →
                            d ≤ yinj i → i < d + e →
                            ∃∃V2.  ⦃G, K⦄ ⊢ V1 ▶*[O, ⫰(d+e-i)] 𝐍⦃V2⦄ & ⇧[O, i+1] V2 ≡ W2.
#G #L #W1 #W2 #d #e * #HW12 #HW2 #K #V1 #i #HLK #HVW1 #Hdi #Hide
elim (cpys_inv_lift1_subst … HW12 … HLK … HVW1) -W1 // #V2 #HV12 #HVW2
lapply (cny_inv_lift_subst … HLK HW2 HVW2) -L
/3 width=3 by ex2_intro, conj/
qed-.
