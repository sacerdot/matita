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

include "basic_2/notation/relations/statictype_6.ma".
include "basic_2/static/da.ma".

(* STRATIFIED STATIC TYPE ASSIGNMENT FOR TERMS ******************************)

(* activate genv *)
inductive ssta (h) (g): relation4 genv lenv term term ≝
| ssta_sort: ∀G,L,k. ssta h g G L (⋆k) (⋆(next h k))
| ssta_ldef: ∀G,L,K,V,U,W,i. ⇩[i] L ≡ K.ⓓV → ssta h g G K V W →
             ⇧[0, i + 1] W ≡ U → ssta h g G L (#i) U
| ssta_ldec: ∀G,L,K,W,U,l,i. ⇩[i] L ≡ K.ⓛW → ⦃G, K⦄ ⊢ W ▪[h, g] l →
             ⇧[0, i + 1] W ≡ U → ssta h g G L (#i) U
| ssta_bind: ∀a,I,G,L,V,T,U. ssta h g G (L.ⓑ{I}V) T U →
             ssta h g G L (ⓑ{a,I}V.T) (ⓑ{a,I}V.U)
| ssta_appl: ∀G,L,V,T,U. ssta h g G L T U → ssta h g G L (ⓐV.T) (ⓐV.U)
| ssta_cast: ∀G,L,W,T,U. ssta h g G L T U → ssta h g G L (ⓝW.T) U
.

interpretation "stratified static type assignment (term)"
   'StaticType h g G L T U = (ssta h g G L T U).

(* Basic inversion lemmas ************************************************)

fact ssta_inv_sort1_aux: ∀h,g,G,L,T,U. ⦃G, L⦄ ⊢ T •[h, g] U → ∀k0. T = ⋆k0 →
                         U = ⋆(next h k0).
#h #g #G #L #T #U * -G -L -T -U
[ #G #L #k #k0 #H destruct //
| #G #L #K #V #U #W #i #_ #_ #_ #k0 #H destruct
| #G #L #K #W #U #l #i #_ #_ #_ #k0 #H destruct
| #a #I #G #L #V #T #U #_ #k0 #H destruct
| #G #L #V #T #U #_ #k0 #H destruct
| #G #L #W #T #U #_ #k0 #H destruct
]
qed-.

lemma ssta_inv_sort1: ∀h,g,G,L,U,k. ⦃G, L⦄ ⊢ ⋆k •[h, g] U → U = ⋆(next h k).
/2 width=6 by ssta_inv_sort1_aux/ qed-.

fact ssta_inv_lref1_aux: ∀h,g,G,L,T,U. ⦃G, L⦄ ⊢ T •[h, g] U → ∀j. T = #j →
                         (∃∃K,V,W. ⇩[j] L ≡ K.ⓓV & ⦃G, K⦄ ⊢ V •[h, g] W &
                                   ⇧[0, j + 1] W ≡ U
                         ) ∨
                         (∃∃K,W,l. ⇩[j] L ≡ K.ⓛW & ⦃G, K⦄ ⊢ W ▪[h, g] l &
                                   ⇧[0, j + 1] W ≡ U
                         ).
#h #g #G #L #T #U * -G -L -T -U
[ #G #L #k #j #H destruct
| #G #L #K #V #U #W #i #HLK #HVW #HWU #j #H destruct /3 width=6 by ex3_3_intro, or_introl/
| #G #L #K #W #U #l #i #HLK #HWl #HWU #j #H destruct /3 width=6 by ex3_3_intro, or_intror/
| #a #I #G #L #V #T #U #_ #j #H destruct
| #G #L #V #T #U #_ #j #H destruct
| #G #L #W #T #U #_ #j #H destruct
]
qed-.

lemma ssta_inv_lref1: ∀h,g,G,L,U,i. ⦃G, L⦄ ⊢ #i •[h, g] U →
                      (∃∃K,V,W. ⇩[i] L ≡ K.ⓓV & ⦃G, K⦄ ⊢ V •[h, g] W &
                                ⇧[0, i + 1] W ≡ U
                      ) ∨
                      (∃∃K,W,l. ⇩[i] L ≡ K.ⓛW & ⦃G, K⦄ ⊢ W ▪[h, g] l &
                                ⇧[0, i + 1] W ≡ U
                      ).
/2 width=3 by ssta_inv_lref1_aux/ qed-.

fact ssta_inv_gref1_aux: ∀h,g,G,L,T,U. ⦃G, L⦄ ⊢ T •[h, g] U → ∀p0. T = §p0 → ⊥.
#h #g #G #L #T #U * -G -L -T -U
[ #G #L #k #p0 #H destruct
| #G #L #K #V #U #W #i #_ #_ #_ #p0 #H destruct
| #G #L #K #W #U #l #i #_ #_ #_ #p0 #H destruct
| #a #I #G #L #V #T #U #_ #p0 #H destruct
| #G #L #V #T #U #_ #p0 #H destruct
| #G #L #W #T #U #_ #p0 #H destruct
]
qed-.

lemma ssta_inv_gref1: ∀h,g,G,L,U,p. ⦃G, L⦄ ⊢ §p •[h, g] U → ⊥.
/2 width=9 by ssta_inv_gref1_aux/ qed-.

fact ssta_inv_bind1_aux: ∀h,g,G,L,T,U. ⦃G, L⦄ ⊢ T •[h, g] U →
                         ∀b,J,X,Y. T = ⓑ{b,J}Y.X →
                         ∃∃Z. ⦃G, L.ⓑ{J}Y⦄ ⊢ X •[h, g] Z & U = ⓑ{b,J}Y.Z.
#h #g #G #L #T #U * -G -L -T -U
[ #G #L #k #b #J #X #Y #H destruct
| #G #L #K #V #U #W #i #_ #_ #_ #b #J #X #Y #H destruct
| #G #L #K #W #U #l #i #_ #_ #_ #b #J #X #Y #H destruct
| #a #I #G #L #V #T #U #HTU #b #J #X #Y #H destruct /2 width=3 by ex2_intro/
| #G #L #V #T #U #_ #b #J #X #Y #H destruct
| #G #L #W #T #U #_ #b #J #X #Y #H destruct
]
qed-.

lemma ssta_inv_bind1: ∀h,g,b,J,G,L,Y,X,U. ⦃G, L⦄ ⊢ ⓑ{b,J}Y.X •[h, g] U →
                      ∃∃Z. ⦃G, L.ⓑ{J}Y⦄ ⊢ X •[h, g] Z & U = ⓑ{b,J}Y.Z.
/2 width=3 by ssta_inv_bind1_aux/ qed-.

fact ssta_inv_appl1_aux: ∀h,g,G,L,T,U. ⦃G, L⦄ ⊢ T •[h, g] U → ∀X,Y. T = ⓐY.X →
                         ∃∃Z. ⦃G, L⦄ ⊢ X •[h, g] Z & U = ⓐY.Z.
#h #g #G #L #T #U * -G -L -T -U
[ #G #L #k #X #Y #H destruct
| #G #L #K #V #U #W #i #_ #_ #_ #X #Y #H destruct
| #G #L #K #W #U #l #i #_ #_ #_ #X #Y #H destruct
| #a #I #G #L #V #T #U #_ #X #Y #H destruct
| #G #L #V #T #U #HTU #X #Y #H destruct /2 width=3 by ex2_intro/
| #G #L #W #T #U #_ #X #Y #H destruct
]
qed-.

lemma ssta_inv_appl1: ∀h,g,G,L,Y,X,U. ⦃G, L⦄ ⊢ ⓐY.X •[h, g] U →
                      ∃∃Z. ⦃G, L⦄ ⊢ X •[h, g] Z & U = ⓐY.Z.
/2 width=3 by ssta_inv_appl1_aux/ qed-.

fact ssta_inv_cast1_aux: ∀h,g,G,L,T,U. ⦃G, L⦄ ⊢ T •[h, g] U → ∀X,Y. T = ⓝY.X →
                         ⦃G, L⦄ ⊢ X •[h, g] U.
#h #g #G #L #T #U * -G -L -T -U
[ #G #L #k #X #Y #H destruct
| #G #L #K #V #U #W #i #_ #_ #_ #X #Y #H destruct
| #G #L #K #W #U #l #i #_ #_ #_ #X #Y #H destruct
| #a #I #G #L #V #T #U #_ #X #Y #H destruct
| #G #L #V #T #U #_ #X #Y #H destruct
| #G #L #W #T #U #HTU #X #Y #H destruct //
]
qed-.

lemma ssta_inv_cast1: ∀h,g,G,L,X,Y,U. ⦃G, L⦄ ⊢ ⓝY.X •[h, g] U → ⦃G, L⦄ ⊢ X •[h, g] U.
/2 width=4 by ssta_inv_cast1_aux/ qed-.

(* Inversion lemmas on degree assignment for terms **************************)

lemma ssta_inv_da: ∀h,g,G,L,T,U. ⦃G, L⦄ ⊢ T •[h, g] U →
                   ∃l. ⦃G, L⦄ ⊢ T ▪[h, g] l.
#h #g #G #L #T #U #H elim H -G -L -T -U
[ #G #L #k elim (deg_total h g k) /3 width=2 by da_sort, ex_intro/
| #G #L #K #V #U #W #i #HLK #_ #_ * /3 width=5 by da_ldef, ex_intro/
| #G #L #K #W #U #l #i #HLK #HWl #_ /3 width=5 by da_ldec, ex_intro/
| #a #I #G #L #V #T #U #_ * /3 width=2 by da_bind, ex_intro/
| #G #L #V #T #U #_ * /3 width=2 by da_flat, ex_intro/
| #G #L #W #T #U #_ * /3 width=2 by da_flat, ex_intro/
]
qed-.

(* Properties on degree assignment for terms ********************************)

lemma da_ssta: ∀h,g,G,L,T,l. ⦃G, L⦄ ⊢ T ▪[h, g] l →
               ∃U. ⦃G, L⦄ ⊢ T •[h, g] U.
#h #g #G #L #T #l #H elim H -G -L -T -l
[ /2 width=2/
| #G #L #K #V #i #l #HLK #_ * #W #HVW
  elim (lift_total W 0 (i+1)) /3 width=7 by ssta_ldef, ex_intro/
| #G #L #K #W #i #l #HLK #HW #_
  elim (lift_total W 0 (i+1)) /3 width=7 by ssta_ldec, ex_intro/
| #a #I #G #L #V #T #l #_ * /3 width=2 by ssta_bind, ex_intro/
| * #G #L #V #T #l #_ * /3 width=2 by ssta_appl, ssta_cast, ex_intro/
]
qed-.

(* Basic_1: removed theorems 7:
            sty0_gen_sort sty0_gen_lref sty0_gen_bind sty0_gen_appl sty0_gen_cast
            sty0_lift sty0_correct
*)
