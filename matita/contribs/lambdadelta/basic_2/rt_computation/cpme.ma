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

include "basic_2/notation/relations/predeval_6.ma".
include "basic_2/rt_transition/cnr.ma".
include "basic_2/rt_computation/cpms.ma".

(* EVALUATION FOR T-BOUND CONTEXT-SENSITIVE PARALLEL RT-TRANSITION ON TERMS *)

(* Basic_2A1: uses: cpre *)
definition cpme (h) (n) (G) (L): relation2 term term ≝
           λT1,T2. ∧∧ ⦃G,L⦄ ⊢ T1 ➡*[n,h] T2 & ⦃G,L⦄ ⊢ ➡[h] 𝐍⦃T2⦄.

interpretation "evaluation for t-bound context-sensitive parallel rt-transition (term)"
   'PRedEval h n G L T1 T2 = (cpme h n G L T1 T2).

(* Basic properties *********************************************************)

lemma cpme_intro (h) (n) (G) (L):
      ∀T1,T2. ⦃G,L⦄ ⊢ T1 ➡*[n,h] T2 → ⦃G,L⦄ ⊢ ➡[h] 𝐍⦃T2⦄ → ⦃G,L⦄⊢T1➡*[h,n]𝐍⦃T2⦄.
/2 width=1 by conj/ qed.

(* Basic forward lemmas *****************************************************)

lemma cpme_fwd_cpms (h) (n) (G) (L):
      ∀T1,T2. ⦃G,L⦄⊢T1➡*[h,n]𝐍⦃T2⦄ → ⦃G,L⦄ ⊢ T1 ➡*[n,h] T2.
#h #n #G #L #T1 #T2 * //
qed-.
