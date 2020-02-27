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

include "basic_2/notation/relations/psubstnormal_5.ma".
include "basic_2/relocation/cpy.ma".

(* NORMAL TERMS FOR CONTEXT-SENSITIVE EXTENDED SUBSTITUTION *****************)

definition cny: ∀d,e. relation3 genv lenv term ≝
                λd,e,G,L. NF … (cpy d e G L) (eq …).

interpretation
   "normality for context-sensitive extended substitution (term)"
   'PSubstNormal G L T d e = (cny d e G L T).

(* Basic inversion lemmas ***************************************************)

lemma cny_inv_lref: ∀G,L,d,e,i. ⦃G, L⦄ ⊢ ▶[d, e] 𝐍⦃#i⦄ →
                    ∨∨ yinj i < d | d + e ≤ yinj i | |L| ≤ i.
#G #L #d #e #i #H elim (ylt_split i d) /2 width=1 by or3_intro0/
#Hdi elim (ylt_split i (d+e)) /2 width=1 by or3_intro1/
#Hide elim (lt_or_ge i (|L|)) /2 width=1 by or3_intro2/
#Hi elim (ldrop_O1_lt L i) //
#I #K #V #HLK elim (lift_total V 0 (i+1))
#W #HVW lapply (H W ?) -H /2 width=5 by cpy_subst/ -HLK
#H destruct elim (lift_inv_lref2_be … HVW) -L -d -e //
qed-.

lemma cny_inv_bind: ∀a,I,G,L,V,T,d,e. ⦃G, L⦄ ⊢ ▶[d, e] 𝐍⦃ⓑ{a,I}V.T⦄ →
                    ⦃G, L⦄ ⊢ ▶[d, e] 𝐍⦃V⦄ ∧ ⦃G, L.ⓑ{I}V⦄ ⊢ ▶[⫯d, e] 𝐍⦃T⦄.
#a #I #G #L #V1 #T1 #d #e #HVT1 @conj
[ #V2 #HV2 lapply (HVT1 (ⓑ{a,I}V2.T1) ?) -HVT1
| #T2 #HT2 lapply (HVT1 (ⓑ{a,I}V1.T2) ?) -HVT1
] 
/2 width=1 by cpy_bind/ #H destruct //
qed-.

lemma cny_inv_flat: ∀I,G,L,V,T,d,e. ⦃G, L⦄ ⊢ ▶[d, e] 𝐍⦃ⓕ{I}V.T⦄ →
                    ⦃G, L⦄ ⊢ ▶[d, e] 𝐍⦃V⦄ ∧ ⦃G, L⦄ ⊢ ▶[d, e] 𝐍⦃T⦄.
#I #G #L #V1 #T1 #d #e #HVT1 @conj
[ #V2 #HV2 lapply (HVT1 (ⓕ{I}V2.T1) ?) -HVT1
| #T2 #HT2 lapply (HVT1 (ⓕ{I}V1.T2) ?) -HVT1
] 
/2 width=1 by cpy_flat/ #H destruct //
qed-.

(* Basic properties *********************************************************)

lemma lsuby_cny_conf: ∀G,d,e.
                      ∀L1,T. ⦃G, L1⦄ ⊢ ▶[d, e] 𝐍⦃T⦄ →
                      ∀L2. L1 ⊑×[d, e] L2 → ⦃G, L2⦄ ⊢ ▶[d, e] 𝐍⦃T⦄.
#G #d #e #L1 #T1 #HT1 #L2 #HL12 #T2 #HT12
@HT1 /3 width=3 by lsuby_cpy_trans/
qed-. 

lemma cny_sort: ∀G,L,d,e,k. ⦃G, L⦄ ⊢ ▶[d, e] 𝐍⦃⋆k⦄.
#G #L #d #e #k #X #H elim (cpy_inv_sort1 … H) -H //
qed.

lemma cny_lref_free: ∀G,L,d,e,i. |L| ≤ i → ⦃G, L⦄ ⊢ ▶[d, e] 𝐍⦃#i⦄.
#G #L #d #e #i #Hi #X #H elim (cpy_inv_lref1 … H) -H // *
#I #K #V #_ #_ #HLK #_ lapply (ldrop_fwd_length_lt2 … HLK) -HLK
#H elim (lt_refl_false i) /2 width=3 by lt_to_le_to_lt/
qed.

lemma cny_lref_atom: ∀G,L,d,e,i. ⇩[i] L ≡ ⋆ → ⦃G, L⦄ ⊢ ▶[d, e] 𝐍⦃#i⦄.
#G #L #d #e #i #HL @cny_lref_free >(ldrop_fwd_length … HL) -HL //
qed.

lemma cny_lref_top: ∀G,L,d,e,i. d+e ≤ yinj i → ⦃G, L⦄ ⊢ ▶[d, e] 𝐍⦃#i⦄.
#G #L #d #e #i #Hdei #X #H elim (cpy_inv_lref1 … H) -H // *
#I #K #V #_ #H elim (ylt_yle_false … H) //
qed.

lemma cny_lref_skip: ∀G,L,d,e,i. yinj i < d → ⦃G, L⦄ ⊢ ▶[d, e] 𝐍⦃#i⦄.
#G #L #d #e #i #Hid #X #H elim (cpy_inv_lref1 … H) -H // *
#I #K #V #H elim (ylt_yle_false … H) //
qed.

lemma cny_gref: ∀G,L,d,e,p. ⦃G, L⦄ ⊢ ▶[d, e] 𝐍⦃§p⦄.
#G #L #d #e #p #X #H elim (cpy_inv_gref1 … H) -H //
qed.

lemma cny_bind: ∀G,L,V,d,e. ⦃G, L⦄ ⊢ ▶[d, e] 𝐍⦃V⦄ →
                ∀I,T. ⦃G, L.ⓑ{I}V⦄ ⊢ ▶[⫯d, e] 𝐍⦃T⦄ →
                ∀a. ⦃G, L⦄ ⊢ ▶[d, e] 𝐍⦃ⓑ{a,I}V.T⦄.
#G #L #V1 #d #e #HV1 #I #T1 #HT1 #a #X #H
elim (cpy_inv_bind1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct
>(HV1 … HV12) -V2 >(HT1 … HT12) -T2 //
qed.

lemma cny_flat: ∀G,L,V,d,e. ⦃G, L⦄ ⊢ ▶[d, e] 𝐍⦃V⦄ →
                ∀T. ⦃G, L⦄ ⊢ ▶[d, e] 𝐍⦃T⦄ →
                ∀I. ⦃G, L⦄ ⊢ ▶[d, e] 𝐍⦃ⓕ{I}V.T⦄.
#G #L #V1 #d #e #HV1 #T1 #HT1 #I #X #H
elim (cpy_inv_flat1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct
>(HV1 … HV12) -V2 >(HT1 … HT12) -T2 //
qed.

lemma cny_narrow: ∀G,L,T,d1,e1. ⦃G, L⦄ ⊢ ▶[d1, e1] 𝐍⦃T⦄ →
                  ∀d2,e2. d1 ≤ d2 → d2 + e2 ≤ d1 + e1 → ⦃G, L⦄ ⊢ ▶[d2, e2] 𝐍⦃T⦄.
#G #L #T1 #d1 #e1 #HT1 #d2 #e2 #Hd12 #Hde21 #T2 #HT12
@HT1 /2 width=5 by cpy_weak/ qed-.
