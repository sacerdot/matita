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

include "basic_2/notation/relations/degree_6.ma".
include "basic_2/grammar/genv.ma".
include "basic_2/substitution/drop.ma".
include "basic_2/static/sd.ma".

(* DEGREE ASSIGNMENT FOR TERMS **********************************************)

(* activate genv *)
inductive da (h:sh) (g:sd h): relation4 genv lenv term nat ≝
| da_sort: ∀G,L,k,l. deg h g k l → da h g G L (⋆k) l
| da_ldef: ∀G,L,K,V,i,l. ⇩[i] L ≡ K.ⓓV → da h g G K V l → da h g G L (#i) l
| da_ldec: ∀G,L,K,W,i,l. ⇩[i] L ≡ K.ⓛW → da h g G K W l → da h g G L (#i) (l+1)
| da_bind: ∀a,I,G,L,V,T,l. da h g G (L.ⓑ{I}V) T l → da h g G L (ⓑ{a,I}V.T) l
| da_flat: ∀I,G,L,V,T,l. da h g G L T l → da h g G L (ⓕ{I}V.T) l
.

interpretation "degree assignment (term)"
   'Degree h g G L T l = (da h g G L T l).

(* Basic inversion lemmas ***************************************************)

fact da_inv_sort_aux: ∀h,g,G,L,T,l. ⦃G, L⦄ ⊢ T ▪[h, g] l →
                      ∀k0. T = ⋆k0 → deg h g k0 l.
#h #g #G #L #T #l * -G -L -T -l
[ #G #L #k #l #Hkl #k0 #H destruct //
| #G #L #K #V #i #l #_ #_ #k0 #H destruct
| #G #L #K #W #i #l #_ #_ #k0 #H destruct
| #a #I #G #L #V #T #l #_ #k0 #H destruct
| #I #G #L #V #T #l #_ #k0 #H destruct
]
qed-.

lemma da_inv_sort: ∀h,g,G,L,k,l. ⦃G, L⦄ ⊢ ⋆k ▪[h, g] l → deg h g k l.
/2 width=5 by da_inv_sort_aux/ qed-.

fact da_inv_lref_aux: ∀h,g,G,L,T,l. ⦃G, L⦄ ⊢ T ▪[h, g] l → ∀j. T = #j →
                      (∃∃K,V. ⇩[j] L ≡ K.ⓓV & ⦃G, K⦄ ⊢ V ▪[h, g] l) ∨
                      (∃∃K,W,l0. ⇩[j] L ≡ K.ⓛW & ⦃G, K⦄ ⊢ W ▪[h, g] l0 &
                                 l = l0 + 1
                       ).
#h #g #G #L #T #l * -G -L -T -l
[ #G #L #k #l #_ #j #H destruct
| #G #L #K #V #i #l #HLK #HV #j #H destruct /3 width=4 by ex2_2_intro, or_introl/
| #G #L #K #W #i #l #HLK #HW #j #H destruct /3 width=6 by ex3_3_intro, or_intror/
| #a #I #G #L #V #T #l #_ #j #H destruct
| #I #G #L #V #T #l #_ #j #H destruct
]
qed-.

lemma da_inv_lref: ∀h,g,G,L,j,l. ⦃G, L⦄ ⊢ #j ▪[h, g] l →
                   (∃∃K,V. ⇩[j] L ≡ K.ⓓV & ⦃G, K⦄ ⊢ V ▪[h, g] l) ∨
                   (∃∃K,W,l0. ⇩[j] L ≡ K.ⓛW & ⦃G, K⦄ ⊢ W ▪[h, g] l0 & l = l0+1).
/2 width=3 by da_inv_lref_aux/ qed-.

fact da_inv_gref_aux: ∀h,g,G,L,T,l. ⦃G, L⦄ ⊢ T ▪[h, g] l → ∀p0. T = §p0 → ⊥.
#h #g #G #L #T #l * -G -L -T -l
[ #G #L #k #l #_ #p0 #H destruct
| #G #L #K #V #i #l #_ #_ #p0 #H destruct
| #G #L #K #W #i #l #_ #_ #p0 #H destruct
| #a #I #G #L #V #T #l #_ #p0 #H destruct
| #I #G #L #V #T #l #_ #p0 #H destruct
]
qed-.

lemma da_inv_gref: ∀h,g,G,L,p,l. ⦃G, L⦄ ⊢ §p ▪[h, g] l → ⊥.
/2 width=9 by da_inv_gref_aux/ qed-.

fact da_inv_bind_aux: ∀h,g,G,L,T,l. ⦃G, L⦄ ⊢ T ▪[h, g] l →
                      ∀b,J,X,Y. T = ⓑ{b,J}Y.X → ⦃G, L.ⓑ{J}Y⦄ ⊢ X ▪[h, g] l.
#h #g #G #L #T #l * -G -L -T -l
[ #G #L #k #l #_ #b #J #X #Y #H destruct
| #G #L #K #V #i #l #_ #_ #b #J #X #Y #H destruct
| #G #L #K #W #i #l #_ #_ #b #J #X #Y #H destruct
| #a #I #G #L #V #T #l #HT #b #J #X #Y #H destruct //
| #I #G #L #V #T #l #_ #b #J #X #Y #H destruct
]
qed-.

lemma da_inv_bind: ∀h,g,b,J,G,L,Y,X,l. ⦃G, L⦄ ⊢ ⓑ{b,J}Y.X ▪[h, g] l → ⦃G, L.ⓑ{J}Y⦄ ⊢ X ▪[h, g] l.
/2 width=4 by da_inv_bind_aux/ qed-.

fact da_inv_flat_aux: ∀h,g,G,L,T,l. ⦃G, L⦄ ⊢ T ▪[h, g] l →
                      ∀J,X,Y. T = ⓕ{J}Y.X → ⦃G, L⦄ ⊢ X ▪[h, g] l.
#h #g #G #L #T #l * -G -L -T -l
[ #G #L #k #l #_ #J #X #Y #H destruct
| #G #L #K #V #i #l #_ #_ #J #X #Y #H destruct
| #G #L #K #W #i #l #_ #_ #J #X #Y #H destruct
| #a #I #G #L #V #T #l #_ #J #X #Y #H destruct
| #I #G #L #V #T #l #HT #J #X #Y #H destruct //
]
qed-.

lemma da_inv_flat: ∀h,g,J,G,L,Y,X,l. ⦃G, L⦄ ⊢ ⓕ{J}Y.X ▪[h, g] l → ⦃G, L⦄ ⊢ X ▪[h, g] l.
/2 width=5 by da_inv_flat_aux/ qed-.
