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
include "basic_2/dynamic/cnv.ma".

(* NATIVE TYPE ASSIGNMENT FOR TERMS *****************************************)

definition nta (h) (a): relation4 genv lenv term term ≝
           λG,L,T,U. ⦃G,L⦄ ⊢ ⓝU.T ![h,a].

interpretation "native type assignment (term)"
  'Colon h a G L T U = (nta h a G L T U).

(* Basic properties *********************************************************)

(* Basic_1: was by definition: ty3_sort *)
(* Basic_2A1: was by definition: nta_sort ntaa_sort *)
lemma nta_sort (h) (a) (G) (L): ∀s. ⦃G,L⦄ ⊢ ⋆s :[h,a] ⋆(⫯[h]s).
#h #a #G #L #s /2 width=3 by cnv_sort, cnv_cast, cpms_sort/
qed.

lemma nta_bind_cnv (h) (a) (G) (K):
      ∀V. ⦃G,K⦄ ⊢ V ![h,a] →
      ∀I,T,U. ⦃G,K.ⓑ{I}V⦄ ⊢ T :[h,a] U →
      ∀p. ⦃G,K⦄ ⊢ ⓑ{p,I}V.T :[h,a] ⓑ{p,I}V.U.
#h #a #G #K #V #HV #I #T #U #H #p
elim (cnv_inv_cast … H) -H #X #HU #HT #HUX #HTX
/3 width=5 by cnv_bind, cnv_cast, cpms_bind_dx/
qed.

(* Basic_2A1: was by definition: nta_cast *)
lemma nta_cast (h) (a) (G) (L):
      ∀T,U. ⦃G,L⦄ ⊢ T :[h,a] U → ⦃G,L⦄ ⊢ ⓝU.T :[h,a] U.
#h #a #G #L #T #U #H
elim (cnv_inv_cast … H) #X #HU #HT #HUX #HTX
/3 width=3 by cnv_cast, cpms_eps/
qed.

(* Basic_1: was by definition: ty3_cast *)
lemma nta_cast_old (h) (a) (G) (L):
      ∀T0,T1. ⦃G,L⦄ ⊢ T0 :[h,a] T1 →
      ∀T2. ⦃G,L⦄ ⊢ T1 :[h,a] T2 → ⦃G,L⦄ ⊢ ⓝT1.T0 :[h,a] ⓝT2.T1.
#h #a #G #L #T0 #T1 #H1 #T2 #H2
elim (cnv_inv_cast … H1) #X1 #_ #_ #HTX1 #HTX01
elim (cnv_inv_cast … H2) #X2 #_ #_ #HTX2 #HTX12
/3 width=3 by cnv_cast, cpms_eps/
qed.

(* Basic inversion lemmas ***************************************************)

lemma nta_inv_gref_sn (h) (a) (G) (L):
      ∀X2,l. ⦃G,L⦄ ⊢ §l :[h,a] X2 → ⊥.
#h #a #G #L #X2 #l #H
elim (cnv_inv_cast … H) -H #X #_ #H #_ #_
elim (cnv_inv_gref … H)
qed-.

(* Basic_forward lemmas *****************************************************)

lemma nta_fwd_cnv_sn (h) (a) (G) (L):
      ∀T,U. ⦃G,L⦄ ⊢ T :[h,a] U → ⦃G,L⦄ ⊢ T ![h,a].
#h #a #G #L #T #U #H
elim (cnv_inv_cast … H) -H #X #_ #HT #_ #_ //
qed-.

(* Note: this is nta_fwd_correct_cnv *)
lemma nta_fwd_cnv_dx (h) (a) (G) (L):
      ∀T,U. ⦃G,L⦄ ⊢ T :[h,a] U → ⦃G,L⦄ ⊢ U ![h,a].
#h #a #G #L #T #U #H
elim (cnv_inv_cast … H) -H #X #HU #_ #_ #_ //
qed-.

(* Basic_1: removed theorems 4:
            ty3_getl_subst0 ty3_fsubst0 ty3_csubst0 ty3_subst0
*)
(* Basic_2A1: removed theorems 2:
   ntaa_nta nta_ntaa
*)
