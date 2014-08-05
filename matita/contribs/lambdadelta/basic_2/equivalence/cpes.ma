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

include "basic_2/notation/relations/dpconvstar_8.ma".
include "basic_2/computation/cpds.ma".

(* DECOMPOSED EXTENDED PARALLEL EQUIVALENCE FOR TERMS ***********************)

definition cpes: ∀h. sd h → nat → nat → relation4 genv lenv term term ≝
                 λh,g,l1,l2,G,L,T1,T2.
                 ∃∃T. ⦃G, L⦄ ⊢ T1 •*➡*[h, g, l1] T & ⦃G, L⦄ ⊢ T2 •*➡*[h, g, l2] T.

interpretation "decomposed extended parallel equivalence (term)"
   'DPConvStar h g l1 l2 G L T1 T2 = (cpes h g l1 l2 G L T1 T2).

(* Basic properties *********************************************************)

lemma cpds_div: ∀h,g,G,L,T1,T2,T,l1,l2.
                ⦃G, L⦄ ⊢ T1 •*➡*[h, g, l1] T → ⦃G, L⦄ ⊢ T2 •*➡*[h, g, l2] T →
                ⦃G, L⦄ ⊢ T1 •*⬌*[h, g, l1, l2] T2.
/2 width=3 by ex2_intro/ qed.

lemma cpes_refl_O_O: ∀h,g,G,L,T,l. ⦃G, L⦄ ⊢ T ▪[h, g] l →
                     ⦃G, L⦄ ⊢ T •*⬌*[h, g, 0, 0] T.
/3 width=3 by cpds_refl, cpds_div/ qed.

lemma cpes_sym: ∀h,g,G,L,T1,T2,l1,l2. ⦃G, L⦄ ⊢ T1 •*⬌*[h, g, l1, l2] T2 →
                ⦃G, L⦄ ⊢ T2 •*⬌*[h, g, l2, l1] T1.
#h #g #G #L #T1 #T2 #L1 #l2 * /2 width=3 by cpds_div/
qed-.
