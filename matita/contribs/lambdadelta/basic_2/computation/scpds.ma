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

include "basic_2/notation/relations/dpredstar_7.ma".
include "basic_2/static/da.ma".
include "basic_2/computation/cprs.ma".

(* STRATIFIED DECOMPOSED PARALLEL COMPUTATION ON TERMS **********************)

definition scpds: ∀h. sd h → nat → relation4 genv lenv term term ≝
                  λh,o,d2,G,L,T1,T2.
                  ∃∃T,d1. d2 ≤ d1 & ⦃G, L⦄ ⊢ T1 ▪[h, o] d1 & ⦃G, L⦄ ⊢ T1 •*[h, d2] T & ⦃G, L⦄ ⊢ T ➡* T2.

interpretation "stratified decomposed parallel computation (term)"
   'DPRedStar h o d G L T1 T2 = (scpds h o d G L T1 T2).

(* Basic properties *********************************************************)

lemma sta_cprs_scpds: ∀h,o,G,L,T1,T,T2,d. ⦃G, L⦄ ⊢ T1 ▪[h, o] d+1 → ⦃G, L⦄ ⊢ T1 •*[h, 1] T →
                      ⦃G, L⦄ ⊢ T ➡* T2 → ⦃G, L⦄ ⊢ T1 •*➡*[h, o, 1] T2.
/2 width=6 by ex4_2_intro/ qed.

lemma lstas_scpds: ∀h,o,G,L,T1,T2,d1. ⦃G, L⦄ ⊢ T1 ▪[h, o] d1 →
                   ∀d2. d2 ≤ d1 → ⦃G, L⦄ ⊢ T1 •*[h, d2] T2 → ⦃G, L⦄ ⊢ T1 •*➡*[h, o, d2] T2.
/2 width=6 by ex4_2_intro/ qed.

lemma scpds_strap1: ∀h,o,G,L,T1,T,T2,d.
                    ⦃G, L⦄ ⊢ T1 •*➡*[h, o, d] T → ⦃G, L⦄ ⊢ T ➡ T2 → ⦃G, L⦄ ⊢ T1 •*➡*[h, o, d] T2.
#h #o #G #L #T1 #T #T2 #d * /3 width=8 by cprs_strap1, ex4_2_intro/
qed.

(* Basic forward lemmas *****************************************************)

lemma scpds_fwd_cprs: ∀h,o,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 •*➡*[h, o, 0] T2 →
                      ⦃G, L⦄ ⊢ T1 ➡* T2.
#h #o #G #L #T1 #T2 * /3 width=3 by cprs_strap2, lstas_cpr/
qed-.
