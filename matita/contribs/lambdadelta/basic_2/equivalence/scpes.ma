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
include "basic_2/computation/scpds.ma".

(* STRATIFIED DECOMPOSED PARALLEL EQUIVALENCE FOR TERMS *********************)

definition scpes: ∀h. sd h → nat → nat → relation4 genv lenv term term ≝
                  λh,g,d1,d2,G,L,T1,T2.
                  ∃∃T. ⦃G, L⦄ ⊢ T1 •*➡*[h, g, d1] T & ⦃G, L⦄ ⊢ T2 •*➡*[h, g, d2] T.

interpretation "stratified decomposed parallel equivalence (term)"
   'DPConvStar h g d1 d2 G L T1 T2 = (scpes h g d1 d2 G L T1 T2).

(* Basic properties *********************************************************)

lemma scpds_div: ∀h,g,G,L,T1,T2,T,d1,d2.
                 ⦃G, L⦄ ⊢ T1 •*➡*[h, g, d1] T → ⦃G, L⦄ ⊢ T2 •*➡*[h, g, d2] T →
                 ⦃G, L⦄ ⊢ T1 •*⬌*[h, g, d1, d2] T2.
/2 width=3 by ex2_intro/ qed.

lemma scpes_sym: ∀h,g,G,L,T1,T2,d1,d2. ⦃G, L⦄ ⊢ T1 •*⬌*[h, g, d1, d2] T2 →
                 ⦃G, L⦄ ⊢ T2 •*⬌*[h, g, d2, d1] T1.
#h #g #G #L #T1 #T2 #L1 #d2 * /2 width=3 by scpds_div/
qed-.
