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

include "basic_2A/notation/relations/degree_6.ma".
include "basic_2A/grammar/genv.ma".
include "basic_2A/substitution/drop.ma".
include "basic_2A/static/sd.ma".

(* DEGREE ASSIGNMENT FOR TERMS **********************************************)

(* activate genv *)
inductive da (h:sh) (g:sd h): relation4 genv lenv term nat ≝
| da_sort: ∀G,L,k,d. deg h g k d → da h g G L (⋆k) d
| da_ldef: ∀G,L,K,V,i,d. ⬇[i] L ≡ K.ⓓV → da h g G K V d → da h g G L (#i) d
| da_ldec: ∀G,L,K,W,i,d. ⬇[i] L ≡ K.ⓛW → da h g G K W d → da h g G L (#i) (d+1)
| da_bind: ∀a,I,G,L,V,T,d. da h g G (L.ⓑ{I}V) T d → da h g G L (ⓑ{a,I}V.T) d
| da_flat: ∀I,G,L,V,T,d. da h g G L T d → da h g G L (ⓕ{I}V.T) d
.

interpretation "degree assignment (term)"
   'Degree h g G L T d = (da h g G L T d).

(* Basic inversion lemmas ***************************************************)

fact da_inv_sort_aux: ∀h,g,G,L,T,d. ⦃G, L⦄ ⊢ T ▪[h, g] d →
                      ∀k0. T = ⋆k0 → deg h g k0 d.
#h #g #G #L #T #d * -G -L -T -d
[ #G #L #k #d #Hkd #k0 #H destruct //
| #G #L #K #V #i #d #_ #_ #k0 #H destruct
| #G #L #K #W #i #d #_ #_ #k0 #H destruct
| #a #I #G #L #V #T #d #_ #k0 #H destruct
| #I #G #L #V #T #d #_ #k0 #H destruct
]
qed-.

lemma da_inv_sort: ∀h,g,G,L,k,d. ⦃G, L⦄ ⊢ ⋆k ▪[h, g] d → deg h g k d.
/2 width=5 by da_inv_sort_aux/ qed-.

fact da_inv_lref_aux: ∀h,g,G,L,T,d. ⦃G, L⦄ ⊢ T ▪[h, g] d → ∀j. T = #j →
                      (∃∃K,V. ⬇[j] L ≡ K.ⓓV & ⦃G, K⦄ ⊢ V ▪[h, g] d) ∨
                      (∃∃K,W,d0. ⬇[j] L ≡ K.ⓛW & ⦃G, K⦄ ⊢ W ▪[h, g] d0 &
                                 d = d0 + 1
                       ).
#h #g #G #L #T #d * -G -L -T -d
[ #G #L #k #d #_ #j #H destruct
| #G #L #K #V #i #d #HLK #HV #j #H destruct /3 width=4 by ex2_2_intro, or_introl/
| #G #L #K #W #i #d #HLK #HW #j #H destruct /3 width=6 by ex3_3_intro, or_intror/
| #a #I #G #L #V #T #d #_ #j #H destruct
| #I #G #L #V #T #d #_ #j #H destruct
]
qed-.

lemma da_inv_lref: ∀h,g,G,L,j,d. ⦃G, L⦄ ⊢ #j ▪[h, g] d →
                   (∃∃K,V. ⬇[j] L ≡ K.ⓓV & ⦃G, K⦄ ⊢ V ▪[h, g] d) ∨
                   (∃∃K,W,d0. ⬇[j] L ≡ K.ⓛW & ⦃G, K⦄ ⊢ W ▪[h, g] d0 & d = d0+1).
/2 width=3 by da_inv_lref_aux/ qed-.

fact da_inv_gref_aux: ∀h,g,G,L,T,d. ⦃G, L⦄ ⊢ T ▪[h, g] d → ∀p0. T = §p0 → ⊥.
#h #g #G #L #T #d * -G -L -T -d
[ #G #L #k #d #_ #p0 #H destruct
| #G #L #K #V #i #d #_ #_ #p0 #H destruct
| #G #L #K #W #i #d #_ #_ #p0 #H destruct
| #a #I #G #L #V #T #d #_ #p0 #H destruct
| #I #G #L #V #T #d #_ #p0 #H destruct
]
qed-.

lemma da_inv_gref: ∀h,g,G,L,p,d. ⦃G, L⦄ ⊢ §p ▪[h, g] d → ⊥.
/2 width=9 by da_inv_gref_aux/ qed-.

fact da_inv_bind_aux: ∀h,g,G,L,T,d. ⦃G, L⦄ ⊢ T ▪[h, g] d →
                      ∀b,J,X,Y. T = ⓑ{b,J}Y.X → ⦃G, L.ⓑ{J}Y⦄ ⊢ X ▪[h, g] d.
#h #g #G #L #T #d * -G -L -T -d
[ #G #L #k #d #_ #b #J #X #Y #H destruct
| #G #L #K #V #i #d #_ #_ #b #J #X #Y #H destruct
| #G #L #K #W #i #d #_ #_ #b #J #X #Y #H destruct
| #a #I #G #L #V #T #d #HT #b #J #X #Y #H destruct //
| #I #G #L #V #T #d #_ #b #J #X #Y #H destruct
]
qed-.

lemma da_inv_bind: ∀h,g,b,J,G,L,Y,X,d. ⦃G, L⦄ ⊢ ⓑ{b,J}Y.X ▪[h, g] d → ⦃G, L.ⓑ{J}Y⦄ ⊢ X ▪[h, g] d.
/2 width=4 by da_inv_bind_aux/ qed-.

fact da_inv_flat_aux: ∀h,g,G,L,T,d. ⦃G, L⦄ ⊢ T ▪[h, g] d →
                      ∀J,X,Y. T = ⓕ{J}Y.X → ⦃G, L⦄ ⊢ X ▪[h, g] d.
#h #g #G #L #T #d * -G -L -T -d
[ #G #L #k #d #_ #J #X #Y #H destruct
| #G #L #K #V #i #d #_ #_ #J #X #Y #H destruct
| #G #L #K #W #i #d #_ #_ #J #X #Y #H destruct
| #a #I #G #L #V #T #d #_ #J #X #Y #H destruct
| #I #G #L #V #T #d #HT #J #X #Y #H destruct //
]
qed-.

lemma da_inv_flat: ∀h,g,J,G,L,Y,X,d. ⦃G, L⦄ ⊢ ⓕ{J}Y.X ▪[h, g] d → ⦃G, L⦄ ⊢ X ▪[h, g] d.
/2 width=5 by da_inv_flat_aux/ qed-.
