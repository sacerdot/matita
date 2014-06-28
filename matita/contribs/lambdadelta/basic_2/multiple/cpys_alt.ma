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

include "basic_2/notation/relations/psubststaralt_6.ma".
include "basic_2/multiple/cpys_lift.ma".

(* CONTEXT-SENSITIVE EXTENDED MULTIPLE SUBSTITUTION FOR TERMS ***************)

(* alternative definition of cpys *)
inductive cpysa: ynat → ynat → relation4 genv lenv term term ≝
| cpysa_atom : ∀I,G,L,d,e. cpysa d e G L (⓪{I}) (⓪{I})
| cpysa_subst: ∀I,G,L,K,V1,V2,W2,i,d,e. d ≤ yinj i → i < d+e →
               ⇩[i] L ≡ K.ⓑ{I}V1 → cpysa 0 (⫰(d+e-i)) G K V1 V2 →
               ⇧[0, i+1] V2 ≡ W2 → cpysa d e G L (#i) W2
| cpysa_bind : ∀a,I,G,L,V1,V2,T1,T2,d,e.
               cpysa d e G L V1 V2 → cpysa (⫯d) e G (L.ⓑ{I}V1) T1 T2 →
               cpysa d e G L (ⓑ{a,I}V1.T1) (ⓑ{a,I}V2.T2)
| cpysa_flat : ∀I,G,L,V1,V2,T1,T2,d,e.
               cpysa d e G L V1 V2 → cpysa d e G L T1 T2 →
               cpysa d e G L (ⓕ{I}V1.T1) (ⓕ{I}V2.T2)
.

interpretation
   "context-sensitive extended multiple substritution (term) alternative"
   'PSubstStarAlt G L T1 d e T2 = (cpysa d e G L T1 T2).

(* Basic properties *********************************************************)

lemma lsuby_cpysa_trans: ∀G,d,e. lsub_trans … (cpysa d e G) (lsuby d e).
#G #d #e #L1 #T1 #T2 #H elim H -G -L1 -T1 -T2 -d -e
[ //
| #I #G #L1 #K1 #V1 #V2 #W2 #i #d #e #Hdi #Hide #HLK1 #_ #HVW2 #IHV12 #L2 #HL12
  elim (lsuby_drop_trans_be … HL12 … HLK1) -HL12 -HLK1 /3 width=7 by cpysa_subst/
| /4 width=1 by lsuby_succ, cpysa_bind/
| /3 width=1 by cpysa_flat/
]
qed-.

lemma cpysa_refl: ∀G,T,L,d,e. ⦃G, L⦄ ⊢ T ▶▶*[d, e] T.
#G #T elim T -T //
#I elim I -I /2 width=1 by cpysa_bind, cpysa_flat/
qed.

lemma cpysa_cpy_trans: ∀G,L,T1,T,d,e. ⦃G, L⦄ ⊢ T1 ▶▶*[d, e] T →
                       ∀T2. ⦃G, L⦄ ⊢ T ▶[d, e] T2 → ⦃G, L⦄ ⊢ T1 ▶▶*[d, e] T2.
#G #L #T1 #T #d #e #H elim H -G -L -T1 -T -d -e
[ #I #G #L #d #e #X #H
  elim (cpy_inv_atom1 … H) -H // * /2 width=7 by cpysa_subst/
| #I #G #L #K #V1 #V2 #W2 #i #d #e #Hdi #Hide #HLK #_ #HVW2 #IHV12 #T2 #H
  lapply (drop_fwd_drop2 … HLK) #H0LK
  lapply (cpy_weak … H 0 (d+e) ? ?) -H // #H
  elim (cpy_inv_lift1_be … H … H0LK … HVW2) -H -H0LK -HVW2
  /3 width=7 by cpysa_subst, ylt_fwd_le_succ/
| #a #I #G #L #V1 #V #T1 #T #d #e #_ #_ #IHV1 #IHT1 #X #H
  elim (cpy_inv_bind1 … H) -H #V2 #T2 #HV2 #HT2 #H destruct
  /5 width=5 by cpysa_bind, lsuby_cpy_trans, lsuby_succ/
| #I #G #L #V1 #V #T1 #T #d #e #_ #_ #IHV1 #IHT1 #X #H
  elim (cpy_inv_flat1 … H) -H #V2 #T2 #HV2 #HT2 #H destruct /3 width=1 by cpysa_flat/
]
qed-.

lemma cpys_cpysa: ∀G,L,T1,T2,d,e. ⦃G, L⦄ ⊢ T1 ▶*[d, e] T2 → ⦃G, L⦄ ⊢ T1 ▶▶*[d, e] T2.
/3 width=8 by cpysa_cpy_trans, cpys_ind/ qed.

(* Basic inversion lemmas ***************************************************)

lemma cpysa_inv_cpys: ∀G,L,T1,T2,d,e. ⦃G, L⦄ ⊢ T1 ▶▶*[d, e] T2 → ⦃G, L⦄ ⊢ T1 ▶*[d, e] T2.
#G #L #T1 #T2 #d #e #H elim H -G -L -T1 -T2 -d -e
/2 width=7 by cpys_subst, cpys_flat, cpys_bind, cpy_cpys/
qed-.

(* Advanced eliminators *****************************************************)

lemma cpys_ind_alt: ∀R:ynat→ynat→relation4 genv lenv term term.
                    (∀I,G,L,d,e. R d e G L (⓪{I}) (⓪{I})) →
                    (∀I,G,L,K,V1,V2,W2,i,d,e. d ≤ yinj i → i < d + e →
                     ⇩[i] L ≡ K.ⓑ{I}V1 → ⦃G, K⦄ ⊢ V1 ▶*[O, ⫰(d+e-i)] V2 →
                     ⇧[O, i+1] V2 ≡ W2 → R O (⫰(d+e-i)) G K V1 V2 → R d e G L (#i) W2
                    ) →
                    (∀a,I,G,L,V1,V2,T1,T2,d,e. ⦃G, L⦄ ⊢ V1 ▶*[d, e] V2 →
                     ⦃G, L.ⓑ{I}V1⦄ ⊢ T1 ▶*[⫯d, e] T2 → R d e G L V1 V2 →
                     R (⫯d) e G (L.ⓑ{I}V1) T1 T2 → R d e G L (ⓑ{a,I}V1.T1) (ⓑ{a,I}V2.T2)
                    ) →
                    (∀I,G,L,V1,V2,T1,T2,d,e. ⦃G, L⦄ ⊢ V1 ▶*[d, e] V2 →
                     ⦃G, L⦄ ⊢ T1 ▶*[d, e] T2 → R d e G L V1 V2 →
                     R d e G L T1 T2 → R d e G L (ⓕ{I}V1.T1) (ⓕ{I}V2.T2)
                    ) →
                    ∀d,e,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ▶*[d, e] T2 → R d e G L T1 T2.
#R #H1 #H2 #H3 #H4 #d #e #G #L #T1 #T2 #H elim (cpys_cpysa … H) -G -L -T1 -T2 -d -e
/3 width=8 by cpysa_inv_cpys/
qed-.
