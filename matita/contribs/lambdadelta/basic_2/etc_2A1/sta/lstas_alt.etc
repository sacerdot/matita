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

include "basic_2/notation/relations/statictypestaralt_6.ma".
include "basic_2/unfold/lstas_lift.ma".

(* NAT-ITERATED STATIC TYPE ASSIGNMENT FOR TERMS ****************************)

(* alternative definition of lstas *)
inductive lstasa (h): genv → relation4 lenv nat term term ≝
| lstasa_O   : ∀G,L,T. lstasa h G L 0 T T
| lstasa_sort: ∀G,L,l,k. lstasa h G L l (⋆k) (⋆((next h)^l k))
| lstasa_ldef: ∀G,L,K,V,W,U,i,l. ⇩[i] L ≡ K.ⓓV → lstasa h G K (l+1) V W →
               ⇧[0, i+1] W ≡ U → lstasa h G L (l+1) (#i) U
| lstasa_ldec: ∀G,L,K,W,V,V0,U,i,l. ⇩[i] L ≡ K.ⓛW → ⦃G, K⦄ ⊢ W •[h] V0 →
               lstasa h G K l W V → ⇧[0, i+1] V ≡ U → lstasa h G L (l+1) (#i) U
| lstasa_bind: ∀a,I,G,L,V,T,U,l. lstasa h G (L.ⓑ{I}V) l T U →
               lstasa h G L l (ⓑ{a,I}V.T) (ⓑ{a,I}V.U)
| lstasa_appl: ∀G,L,V,T,U,l. lstasa h G L l T U → lstasa h G L l (ⓐV.T) (ⓐV.U)
| lstasa_cast: ∀G,L,W,T,U,l. lstasa h G L (l+1) T U → lstasa h G L (l+1) (ⓝW.T) U
.

interpretation "nat-iterated static type assignment (term) alternative"
   'StaticTypeStarAlt h G L l T U = (lstasa h G L l T U).

(* Base properties **********************************************************)

lemma sta_lstasa: ∀h,G,L,T,U. ⦃G, L⦄ ⊢ T •[h] U → ⦃G, L⦄ ⊢ T ••*[h, 1] U.
#h #G #L #T #U #H elim H -G -L -T -U
/2 width=8 by lstasa_O, lstasa_sort, lstasa_ldef, lstasa_ldec, lstasa_bind, lstasa_appl, lstasa_cast/
qed.

lemma lstasa_step_dx: ∀h,G,L,T1,T,l. ⦃G, L⦄ ⊢ T1 ••*[h, l] T →
                      ∀T2. ⦃G, L⦄ ⊢ T •[h] T2 → ⦃G, L⦄ ⊢ T1 ••*[h, l+1] T2.
#h #G #L #T1 #T #l #H elim H -G -L -T1 -T -l
[ /2 width=1 by sta_lstasa/
| #G #L #l #k #X #H >(sta_inv_sort1 … H) -X >commutative_plus //
| #G #L #K #V #W #U #i #l #HLK #_ #HWU #IHVW #U2 #HU2
  lapply (drop_fwd_drop2 … HLK) #H
  elim (sta_inv_lift1 … HU2 … H … HWU) -H -U /3 width=6 by lstasa_ldef/
| #G #L #K #W #V #V0 #U #i #l #HLK #HWl0 #_ #HVU #IHWV #U2 #HU2
  lapply (drop_fwd_drop2 … HLK) #H
  elim (sta_inv_lift1 … HU2 … H … HVU) -H -U /3 width=8 by lstasa_ldec/
| #a #I #G #L #V #T1 #U1 #l #_ #IHTU1 #X #H
  elim (sta_inv_bind1 … H) -H #U #HU1 #H destruct /3 width=1 by lstasa_bind/
| #G #L #V #T1 #U1 #l #_ #IHTU1 #X #H
  elim (sta_inv_appl1 … H) -H #U #HU1 #H destruct /3 width=1 by lstasa_appl/
| /3 width=1 by lstasa_cast/
]
qed.

(* Main properties **********************************************************)

theorem lstas_lstasa: ∀h,G,L,T,U,l. ⦃G, L⦄ ⊢ T •*[h, l] U → ⦃G, L⦄ ⊢ T ••*[h, l] U.
#h #G #L #T #U #l #H @(lstas_ind_dx … H) -U -l /2 width=3 by lstasa_step_dx, lstasa_O/
qed.

(* Main inversion lemmas ****************************************************)

theorem lstasa_inv_lstas: ∀h,G,L,T,U,l. ⦃G, L⦄ ⊢ T ••*[h, l] U → ⦃G, L⦄ ⊢ T •*[h, l] U.
#h #G #L #T #U #l #H elim H -G -L -T -U -l
/2 width=8 by lstas_inv_SO, lstas_ldec, lstas_ldef, lstas_cast, lstas_appl, lstas_bind/
qed-.

(* Advanced eliminators *****************************************************)

lemma lstas_ind_alt: ∀h. ∀R:genv→relation4 lenv nat term term.
                     (∀G,L,T. R G L O T T) →
                     (∀G,L,l,k. R G L l (⋆k) (⋆((next h)^l k))) → (
                        ∀G,L,K,V,W,U,i,l.
                        ⇩[i] L ≡ K.ⓓV → ⦃G, K⦄ ⊢ V •*[h, l+1] W → ⇧[O, i+1] W ≡ U →
                        R G K (l+1) V W → R G L (l+1) (#i) U
                     ) → (
                        ∀G,L,K,W,V,V0,U,i,l.
                        ⇩[i] L ≡ K.ⓛW → ⦃G, K⦄ ⊢ W •[h] V0 →
                        ⦃G, K⦄ ⊢ W •*[h, l]V → ⇧[O, i+1] V ≡ U →
                        R G K l W V → R G L (l+1) (#i) U
                     ) → (
                        ∀a,I,G,L,V,T,U,l. ⦃G, L.ⓑ{I}V⦄ ⊢ T •*[h, l] U →
                        R G (L.ⓑ{I}V) l T U → R G L l (ⓑ{a,I}V.T) (ⓑ{a,I}V.U)
                     ) → (
                        ∀G,L,V,T,U,l. ⦃G, L⦄ ⊢ T •*[h, l] U →
                        R G L l T U → R G L l (ⓐV.T) (ⓐV.U)
                     ) → (
                        ∀G,L,W,T,U,l. ⦃G, L⦄⊢ T •*[h, l+1] U →
                        R G L (l+1) T U → R G L (l+1) (ⓝW.T) U
                     ) →
                     ∀G,L,l,T,U. ⦃G, L⦄ ⊢ T •*[h, l] U → R G L l T U.
#h #R #IH1 #IH2 #IH3 #IH4 #IH5 #IH6 #IH7 #G #L #l #T #U #H
elim (lstas_lstasa … H) /3 width=10 by lstasa_inv_lstas/
qed-.
