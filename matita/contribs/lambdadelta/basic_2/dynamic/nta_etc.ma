(*
(* Advanced inversion lemmas ************************************************)


(* Basic_1: was ty3_gen_lref *)
lemma nta_inv_lref1: ∀h,L,U,i. ⦃h, L⦄ ⊢ #i : U →
                     (∃∃K,V,W,U0. ⇩[0, i] L ≡ K. ⓓV & ⦃h, K⦄ ⊢ V : W &
                                  ⇧[0, i + 1] W ≡ U0 & L ⊢ U0 ⬌* U
                     ) ∨
                     (∃∃K,W,V,U0. ⇩[0, i] L ≡ K. ⓛW & ⦃h, K⦄ ⊢ W : V &
                                  ⇧[0, i + 1] W ≡ U0 & L ⊢ U0 ⬌* U
                     ).
/2 width=3/ qed-.

(* Advanced forvard lemmas **************************************************)

lemma nta_fwd_pure1: ∀h,L,X,Y,U. ⦃h, L⦄ ⊢ ⓐY.X : U →
                     ∃∃V,W. ⦃h, L⦄ ⊢ Y : W & ⦃h, L⦄ ⊢ X : V & L ⊢ ⓐY.V ⬌* U.
/2 width=3/ qed-.

lemma nta_ind_alt: ∀h. ∀R:lenv→relation term.
   (∀L,k. R L ⋆k ⋆(next h k)) →
   (∀L,K,V,W,U,i.
      ⇩[O, i] L ≡ K.ⓓV → ⦃h, K⦄ ⊢ V : W → ⇧[O, i + 1] W ≡ U →
      R K V W → R L (#i) U 
   ) →
   (∀L,K,W,V,U,i.
      ⇩[O, i] L ≡ K.ⓛW → ⦃h, K⦄ ⊢ W : V → ⇧[O, i + 1] W ≡ U →
      R K W V → R L (#i) U
   ) →
   (∀I,L,V,W,T,U.
      ⦃h, L⦄ ⊢ V : W → ⦃h, L.ⓑ{I}V⦄ ⊢ T : U →
      R L V W → R (L.ⓑ{I}V) T U → R L (ⓑ{I}V.T) (ⓑ{I}V.U)
   ) →
   (∀L,V,W,T,U.
      ⦃h, L⦄ ⊢ V : W → ⦃h, L⦄ ⊢ (ⓛW.T):(ⓛW.U) →
      R L V W →R L (ⓛW.T) (ⓛW.U) →R L (ⓐV.ⓛW.T) (ⓐV.ⓛW.U)
   ) →
   (∀L,V,W,T,U.
      ⦃h, L⦄ ⊢ T : U → ⦃h, L⦄ ⊢ (ⓐV.U) : W →
      R L T U → R L (ⓐV.U) W → R L (ⓐV.T) (ⓐV.U)
   ) →
   (∀L,T,U,W.
      ⦃h, L⦄ ⊢ T : U → ⦃h, L⦄ ⊢ U : W →
      R L T U → R L U W → R L (ⓝU.T) U
   ) →
   (∀L,T,U1,U2,V2.
      ⦃h, L⦄ ⊢ T : U1 → L ⊢ U1 ⬌* U2 → ⦃h, L⦄ ⊢ U2 : V2 →
      R L T U1 →R L U2 V2 →R L T U2
   ) →
   ∀L,T,U. ⦃h, L⦄ ⊢ T : U → R L T U.
#h #R #H1 #H2 #H3 #H4 #H5 #H6 #H7 #H8 #L #T #U #H elim (nta_ntaa … H) -L -T -U
// /3 width=1 by ntaa_nta/ /3 width=3 by ntaa_nta/ /3 width=4 by ntaa_nta/
/3 width=7 by ntaa_nta/
qed-.

*)
