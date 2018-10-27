(*
(* Advanced forvard lemmas **************************************************)

lemma nta_fwd_pure1: ∀h,L,X,Y,U. ⦃h, L⦄ ⊢ ⓐY.X : U →
                     ∃∃V,W. ⦃h, L⦄ ⊢ Y : W & ⦃h, L⦄ ⊢ X : V & L ⊢ ⓐY.V ⬌* U.
/2 width=3/ qed-.

*)
