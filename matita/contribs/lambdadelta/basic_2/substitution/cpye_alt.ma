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

include "basic_2/notation/relations/psubstevalalt_6.ma".
include "basic_2/substitution/cpye_lift.ma".

(* EVALUATION FOR CONTEXT-SENSITIVE EXTENDED SUBSTITUTION ON TERMS **********)

(* Note: alternative definition of cpye *)
inductive cpyea: ynat → ynat → relation4 genv lenv term term ≝
| cpyea_sort : ∀G,L,d,e,k. cpyea d e G L (⋆k) (⋆k)
| cpyea_free : ∀G,L,d,e,i. |L| ≤ i → cpyea d e G L (#i) (#i)
| cpyea_top  : ∀G,L,d,e,i. d + e ≤ yinj i → cpyea d e G L (#i) (#i)
| cpyea_skip : ∀G,L,d,e,i. yinj i < d → cpyea d e G L (#i) (#i)
| cpyea_subst: ∀I,G,L,K,V1,V2,W2,i,d,e. d ≤ yinj i → yinj i < d+e →
               ⇩[i] L ≡ K.ⓑ{I}V1 → cpyea (yinj 0) (⫰(d+e-yinj i)) G K V1 V2 →
               ⇧[0, i+1] V2 ≡ W2 → cpyea d e G L (#i) W2
| cpyea_gref : ∀G,L,d,e,p. cpyea d e G L (§p) (§p)
| cpyea_bind : ∀a,I,G,L,V1,V2,T1,T2,d,e.
               cpyea d e G L V1 V2 → cpyea (⫯d) e G (L.ⓑ{I}V1) T1 T2 →
               cpyea d e G L (ⓑ{a,I}V1.T1) (ⓑ{a,I}V2.T2)
| cpyea_flat : ∀I,G,L,V1,V2,T1,T2,d,e.
               cpyea d e G L V1 V2 → cpyea d e G L T1 T2 →
               cpyea d e G L (ⓕ{I}V1.T1) (ⓕ{I}V2.T2)
.

interpretation
   "evaluation for context-sensitive extended substitution (term) alternative"
   'PSubstEvalAlt G L T1 T2 d e = (cpyea d e G L T1 T2).

(* Main properties **********************************************************)

theorem cpye_cpyea: ∀G,L,T1,T2,d,e. ⦃G, L⦄ ⊢ T1 ▶*[d, e] 𝐍⦃T2⦄ → ⦃G, L⦄ ⊢ T1 ▶▶*[d, e] 𝐍⦃T2⦄.
#G #L #T1 @(fqup_wf_ind_eq … G L T1) -G -L -T1
#Z #Y #X #IH #G #L * *
[ #k #_ #_ #_ #T2 #d #e #H -X -Y -Z >(cpye_inv_sort1 … H) -H //
| #i #HG #HL #HT #T2 #d #e #H destruct
  elim (cpye_inv_lref1 … H) -H *
  /4 width=7 by cpyea_subst, cpyea_free, cpyea_top, cpyea_skip, fqup_lref/
| #p #_ #_ #_ #T2 #d #e #H -X -Y -Z >(cpye_inv_gref1 … H) -H //
| #a #I #V1 #T1 #HG #HL #HT #T #d #e #H destruct
  elim (cpye_inv_bind1 … H) -H /3 width=1 by cpyea_bind/
| #I #V1 #T1 #HG #HL #HT #T #d #e #H destruct
  elim (cpye_inv_flat1 … H) -H /3 width=1 by cpyea_flat/
]
qed.

(* Main inversion properties ************************************************)

theorem cpyea_inv_cpye: ∀G,L,T1,T2,d,e. ⦃G, L⦄ ⊢ T1 ▶▶*[d, e] 𝐍⦃T2⦄ → ⦃G, L⦄ ⊢ T1 ▶*[d, e] 𝐍⦃T2⦄.
#G #L #T1 #T2 #d #e #H elim H -G -L -T1 -T2 -d -e
/2 width=7 by cpye_subst, cpye_flat, cpye_bind, cpye_skip, cpye_top, cpye_free/
qed-.

(* Advanced eliminators *****************************************************)

lemma cpye_ind_alt: ∀R:ynat→ynat→relation4 genv lenv term term.
                    (∀G,L,d,e,k. R d e G L (⋆k) (⋆k)) →
                    (∀G,L,d,e,i. |L| ≤ i → R d e G L (#i) (#i)) →
                    (∀G,L,d,e,i. d + e ≤ yinj i → R d e G L (#i) (#i)) →
                    (∀G,L,d,e,i. yinj i < d → R d e G L (#i) (#i)) →
                    (∀I,G,L,K,V1,V2,W2,i,d,e. d ≤ yinj i → yinj i < d + e →
                     ⇩[i] L ≡ K.ⓑ{I}V1 → ⦃G, K⦄ ⊢ V1 ▶*[yinj O, ⫰(d+e-yinj i)] 𝐍⦃V2⦄ →
                     ⇧[O, i+1] V2 ≡ W2 → R (yinj O) (⫰(d+e-yinj i)) G K V1 V2 → R d e G L (#i) W2
                    ) →
                    (∀G,L,d,e,p. R d e G L (§p) (§p)) →
                    (∀a,I,G,L,V1,V2,T1,T2,d,e. ⦃G, L⦄ ⊢ V1 ▶*[d, e] 𝐍⦃V2⦄ →
                     ⦃G, L.ⓑ{I}V1⦄ ⊢ T1 ▶*[⫯d, e] 𝐍⦃T2⦄ → R d e G L V1 V2 →
                     R (⫯d) e G (L.ⓑ{I}V1) T1 T2 → R d e G L (ⓑ{a,I}V1.T1) (ⓑ{a,I}V2.T2)
                    ) →
                    (∀I,G,L,V1,V2,T1,T2,d,e. ⦃G, L⦄ ⊢ V1 ▶*[d, e] 𝐍⦃V2⦄ →
                     ⦃G, L⦄ ⊢ T1 ▶*[d, e] 𝐍⦃T2⦄ → R d e G L V1 V2 →
                     R d e G L T1 T2 → R d e G L (ⓕ{I}V1.T1) (ⓕ{I}V2.T2)
                    ) →
                    ∀d,e,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ▶*[d, e] 𝐍⦃T2⦄ → R d e G L T1 T2.
#R #H1 #H2 #H3 #H4 #H5 #H6 #H7 #H8 #d #e #G #L #T1 #T2 #H elim (cpye_cpyea … H) -G -L -T1 -T2 -d -e
/3 width=8 by cpyea_inv_cpye/
qed-.
