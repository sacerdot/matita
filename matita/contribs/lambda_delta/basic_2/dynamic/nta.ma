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

include "basic_2/static/sh.ma".
include "basic_2/equivalence/cpcs.ma".

(* NATIVE TYPE ASSIGNMENT ON TERMS ******************************************)

inductive nta (h:sh): lenv → relation term ≝
| nta_sort: ∀L,k. nta h L (⋆k) (⋆(next h k))
| nta_ldef: ∀L,K,V,W,U,i. ⇩[0, i] L ≡ K. ⓓV → nta h K V W →
            ⇧[0, i + 1] W ≡ U → nta h L (#i) U
| nta_ldec: ∀L,K,W,V,U,i. ⇩[0, i] L ≡ K. ⓛW → nta h K W V →
            ⇧[0, i + 1] W ≡ U → nta h L (#i) U
| nta_bind: ∀I,L,V,W,T,U. nta h L V W → nta h (L. ⓑ{I} V) T U →
            nta h L (ⓑ{I}V.T) (ⓑ{I}V.U)
| nta_appl: ∀L,V,W,T,U. nta h L V W → nta h L (ⓛW.T) (ⓛW.U) →
            nta h L (ⓐV.ⓛW.T) (ⓐV.ⓛW.U)
| nta_pure: ∀L,V,W,T,U. nta h L T U → nta h L (ⓐV.U) W →
            nta h L (ⓐV.T) (ⓐV.U)
| nta_cast: ∀L,T,U. nta h L T U → nta h L (ⓝU. T) U
| nta_conv: ∀L,T,U1,U2,V2. nta h L T U1 → L ⊢ U1 ⬌* U2 → nta h L U2 V2 →
            nta h L T U2
.

interpretation "native type assignment (term)"
   'NativeType h L T U = (nta h L T U).

(* Basic properties *********************************************************)

(* Basic_1: was: ty3_cast *)
lemma nta_cast_old: ∀h,L,W,T,U.
                    ⦃h, L⦄ ⊢ T : U → ⦃h, L⦄ ⊢ U : W → ⦃h, L⦄ ⊢ ⓝU.T : ⓝW.U.
/4 width=3/ qed.

(* Basic_1: was: ty3_typecheck *)
lemma nta_typecheck: ∀h,L,T,U. ⦃h, L⦄ ⊢ T : U → ∃T0. ⦃h, L⦄ ⊢ ⓝU.T : T0.
/3 width=2/ qed.

(* Basic_1: removed theorems 4:
            ty3_getl_subst0 ty3_fsubst0 ty3_csubst0 ty3_subst0
*)
