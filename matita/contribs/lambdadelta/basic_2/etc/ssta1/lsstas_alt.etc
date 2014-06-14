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

include "basic_2/notation/relations/statictypestaralt_7.ma".
include "basic_2/unfold/lsstas_lift.ma".

(* NAT-ITERATED STRATIFIED STATIC TYPE ASSIGNMENT FOR TERMS *****************)

(* alternative definition of lsstas *)
inductive lsstasa (h) (g): genv → relation4 lenv nat term term ≝
| lsstasa_O   : ∀G,L,T. lsstasa h g G L 0 T T
| lsstasa_sort: ∀G,L,l,k. lsstasa h g G L l (⋆k) (⋆((next h)^l k))
| lsstasa_ldef: ∀G,L,K,V,W,U,i,l. ⇩[i] L ≡ K.ⓓV → lsstasa h g G K (l+1) V W →
                ⇧[0, i+1] W ≡ U → lsstasa h g G L (l+1) (#i) U
| lsstasa_ldec: ∀G,L,K,W,V,U,i,l,l0. ⇩[i] L ≡ K.ⓛW → ⦃G, K⦄ ⊢ W ▪[h, g] l0 →
                lsstasa h g G K l W V → ⇧[0, i+1] V ≡ U → lsstasa h g G L (l+1) (#i) U
| lsstasa_bind: ∀a,I,G,L,V,T,U,l. lsstasa h g G (L.ⓑ{I}V) l T U →
                lsstasa h g G L l (ⓑ{a,I}V.T) (ⓑ{a,I}V.U)
| lsstasa_appl: ∀G,L,V,T,U,l. lsstasa h g G L l T U → lsstasa h g G L l (ⓐV.T) (ⓐV.U)
| lsstasa_cast: ∀G,L,W,T,U,l. lsstasa h g G L (l+1) T U → lsstasa h g G L (l+1) (ⓝW.T) U
.

interpretation "nat-iterated stratified static type assignment (term) alternative"
   'StaticTypeStarAlt h g G L l T U = (lsstasa h g G L l T U).

(* Base properties **********************************************************)

lemma ssta_lsstasa: ∀h,g,G,L,T,U. ⦃G, L⦄ ⊢ T •[h, g] U → ⦃G, L⦄ ⊢ T ••*[h, g, 1] U.
#h #g #G #L #T #U #H elim H -G -L -T -U
/2 width=8 by lsstasa_O, lsstasa_sort, lsstasa_ldef, lsstasa_ldec, lsstasa_bind, lsstasa_appl, lsstasa_cast/
qed.

lemma lsstasa_step_dx: ∀h,g,G,L,T1,T,l. ⦃G, L⦄ ⊢ T1 ••*[h, g, l] T →
                       ∀T2. ⦃G, L⦄ ⊢ T •[h, g] T2 → ⦃G, L⦄ ⊢ T1 ••*[h, g, l+1] T2.
#h #g #G #L #T1 #T #l #H elim H -G -L -T1 -T -l
[ /2 width=1/
| #G #L #l #k #X #H >(ssta_inv_sort1 … H) -X >commutative_plus //
| #G #L #K #V #W #U #i #l #HLK #_ #HWU #IHVW #U2 #HU2
  lapply (ldrop_fwd_drop2 … HLK) #H
  elim (ssta_inv_lift1 … HU2 … H … HWU) -H -U /3 width=6 by lsstasa_ldef/
| #G #L #K #W #V #U #i #l #l0 #HLK #HWl0 #_ #HVU #IHWV #U2 #HU2
  lapply (ldrop_fwd_drop2 … HLK) #H
  elim (ssta_inv_lift1 … HU2 … H … HVU) -H -U /3 width=8 by lsstasa_ldec/
| #a #I #G #L #V #T1 #U1 #l #_ #IHTU1 #X #H
  elim (ssta_inv_bind1 … H) -H #U #HU1 #H destruct /3 width=1 by lsstasa_bind/
| #G #L #V #T1 #U1 #l #_ #IHTU1 #X #H
  elim (ssta_inv_appl1 … H) -H #U #HU1 #H destruct /3 width=1 by lsstasa_appl/
| /3 width=1 by lsstasa_cast/
]
qed.

(* Main properties **********************************************************)

theorem lsstas_lsstasa: ∀h,g,G,L,T,U,l. ⦃G, L⦄ ⊢ T •*[h, g, l] U → ⦃G, L⦄ ⊢ T ••*[h, g, l] U.
#h #g #G #L #T #U #l #H @(lsstas_ind_dx … H) -U -l /2 width=3 by lsstasa_step_dx, lsstasa_O/
qed.

(* Main inversion lemmas ****************************************************)

theorem lsstasa_inv_lsstas: ∀h,g,G,L,T,U,l. ⦃G, L⦄ ⊢ T ••*[h, g, l] U → ⦃G, L⦄ ⊢ T •*[h, g, l] U.
#h #g #G #L #T #U #l #H elim H -G -L -T -U -l
/2 width=8 by lsstas_inv_SO, lsstas_ldec, lsstas_ldef, lsstas_cast, lsstas_appl, lsstas_bind/
qed-.

(* Advanced eliminators *****************************************************)

lemma lsstas_ind_alt: ∀h,g. ∀R:genv→relation4 lenv nat term term.
                      (∀G,L,T. R G L O T T) →
                      (∀G,L,l,k. R G L l (⋆k) (⋆((next h)^l k))) → (
                         ∀G,L,K,V,W,U,i,l.
                         ⇩[i] L ≡ K.ⓓV → ⦃G, K⦄ ⊢ V •*[h, g, l+1] W → ⇧[O, i+1] W ≡ U →
                         R G K (l+1) V W → R G L (l+1) (#i) U
                      ) → (
                         ∀G,L,K,W,V,U,i,l,l0.
                         ⇩[i] L ≡ K.ⓛW → ⦃G, K⦄ ⊢ W ▪[h, g] l0 →
                         ⦃G, K⦄ ⊢ W •*[h, g, l]V → ⇧[O, i+1] V ≡ U →
                         R G K l W V → R G L (l+1) (#i) U
                      ) → (
                         ∀a,I,G,L,V,T,U,l. ⦃G, L.ⓑ{I}V⦄ ⊢ T •*[h, g, l] U →
                         R G (L.ⓑ{I}V) l T U → R G L l (ⓑ{a,I}V.T) (ⓑ{a,I}V.U)
                      ) → (
                         ∀G,L,V,T,U,l. ⦃G, L⦄ ⊢ T •*[h, g, l] U →
                         R G L l T U → R G L l (ⓐV.T) (ⓐV.U)
                      ) → (
                         ∀G,L,W,T,U,l. ⦃G, L⦄⊢ T •*[h, g, l+1] U →
                         R G L (l+1) T U → R G L (l+1) (ⓝW.T) U
                      ) →
                      ∀G,L,l,T,U. ⦃G, L⦄ ⊢ T •*[h, g, l] U → R G L l T U.
#h #g #R #IH1 #IH2 #IH3 #IH4 #IH5 #IH6 #IH7 #G #L #l #T #U #H
elim (lsstas_lsstasa … H) /3 width=10 by lsstasa_inv_lsstas/
qed-.
