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

include "basic_2/notation/relations/colon_6.ma".
include "basic_2/notation/relations/colon_5.ma".
include "basic_2/notation/relations/colonstar_5.ma".
include "basic_2/dynamic/cnv.ma".

(* NATIVE TYPE ASSIGNMENT FOR TERMS *****************************************)

definition nta (a) (h): relation4 genv lenv term term ≝
                        λG,L,T,U. ⦃G,L⦄ ⊢ ⓝU.T ![a,h].

interpretation "native type assignment (term)"
   'Colon a h G L T U = (nta a h G L T U).

interpretation "restricted native type assignment (term)"
   'Colon h G L T U = (nta true h G L T U).

interpretation "extended native type assignment (term)"
   'ColonStar h G L T U = (nta false h G L T U).

(* Basic properties *********************************************************)

(* Basic_1: was by definition: ty3_sort *)
(* Basic_2A1: was by definition: nta_sort ntaa_sort *)
lemma nta_sort (a) (h) (G) (L) (s): ⦃G,L⦄ ⊢ ⋆s :[a,h] ⋆(next h s).
#a #h #G #L #s /2 width=3 by cnv_sort, cnv_cast, cpms_sort/
qed.

lemma nta_bind_cnv (a) (h) (G) (K):
      ∀V. ⦃G,K⦄ ⊢ V ![a,h] →
      ∀I,T,U. ⦃G,K.ⓑ{I}V⦄ ⊢ T :[a,h] U →
      ∀p. ⦃G,K⦄ ⊢ ⓑ{p,I}V.T :[a,h] ⓑ{p,I}V.U.
#a #h #G #K #V #HV #I #T #U #H #p
elim (cnv_inv_cast … H) -H #X #HU #HT #HUX #HTX
/3 width=5 by cnv_bind, cnv_cast, cpms_bind_dx/
qed.

(* Basic_2A1: was by definition: nta_cast *)
lemma nta_cast (a) (h) (G) (L):
      ∀T,U. ⦃G,L⦄ ⊢ T :[a,h] U → ⦃G,L⦄ ⊢ ⓝU.T :[a,h] U.
#a #h #G #L #T #U #H
elim (cnv_inv_cast … H) #X #HU #HT #HUX #HTX
/3 width=3 by cnv_cast, cpms_eps/
qed.

(* Basic_1: was by definition: ty3_cast *)
lemma nta_cast_old (a) (h) (G) (L):
      ∀T0,T1. ⦃G,L⦄ ⊢ T0 :[a,h] T1 →
      ∀T2. ⦃G,L⦄ ⊢ T1 :[a,h] T2 → ⦃G,L⦄ ⊢ ⓝT1.T0 :[a,h] ⓝT2.T1.
#a #h #G #L #T0 #T1 #H1 #T2 #H2
elim (cnv_inv_cast … H1) #X1 #_ #_ #HTX1 #HTX01
elim (cnv_inv_cast … H2) #X2 #_ #_ #HTX2 #HTX12
/3 width=3 by cnv_cast, cpms_eps/
qed.

(* Basic_forward lemmas *****************************************************)

lemma nta_fwd_cnv_sn (a) (h) (G) (L):
                     ∀T,U. ⦃G,L⦄ ⊢ T :[a,h] U → ⦃G,L⦄ ⊢ T ![a,h].
#a #h #G #L #T #U #H
elim (cnv_inv_cast … H) -H #X #_ #HT #_ #_ //
qed-.

(* Note: this is nta_fwd_correct_cnv *)
lemma nta_fwd_cnv_dx (a) (h) (G) (L):
                     ∀T,U. ⦃G,L⦄ ⊢ T :[a,h] U → ⦃G,L⦄ ⊢ U ![a,h].
#a #h #G #L #T #U #H
elim (cnv_inv_cast … H) -H #X #HU #_ #_ #_ //
qed-.

(*

| nta_ldef: ∀L,K,V,W,U,i. ⇩[0, i] L ≡ K. ⓓV → nta h K V W →
            ⇧[0, i + 1] W ≡ U → nta h L (#i) U
| nta_ldec: ∀L,K,W,V,U,i. ⇩[0, i] L ≡ K. ⓛW → nta h K W V →
            ⇧[0, i + 1] W ≡ U → nta h L (#i) U
.

(* Basic properties *********************************************************)

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

(* Basic_1: removed theorems 4:
            ty3_getl_subst0 ty3_fsubst0 ty3_csubst0 ty3_subst0
*)
(* Basic_2A1: removed theorems 2:
   ntaa_nta nta_ntaa
*)
