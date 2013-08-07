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

include "basic_2/unfold/sstas_lift.ma".
include "basic_2/dynamic/snv.ma".

(* STRATIFIED NATIVE VALIDITY FOR TERMS *************************************)

(* Forward_lemmas on iterated stratified static type assignment for terms ***)

lemma snv_sstas_fwd_correct: ∀h,g,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ¡[h, g] → ⦃G, L⦄ ⊢ T1 •* [h, g] T2 →
                             ∃∃U2,l. ⦃G, L⦄ ⊢ T2 •[h, g] ⦃l, U2⦄.
#h #g #G #L #T1 #T2 #HT1 #HT12
elim (snv_fwd_ssta … HT1) -HT1 /2 width=5 by sstas_fwd_correct/
qed-.
