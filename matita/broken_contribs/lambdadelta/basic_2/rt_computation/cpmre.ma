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
definition cpmre (h) (n) (G) (L): relation2 term term ≝
           λT1,T2. ∧∧ ❨G,L❩ ⊢ T1 ➡*[h,n] T2 & ❨G,L❩ ⊢ ➡𝐍[h,0] T2.

interpretation "evaluation for t-bound context-sensitive parallel rt-transition (term)"
   'PRedEval h n G L T1 T2 = (cpmre h n G L T1 T2).

(* Basic properties *********************************************************)

lemma cpmre_intro (h) (n) (G) (L):
      ∀T1,T2. ❨G,L❩ ⊢ T1 ➡*[h,n] T2 → ❨G,L❩ ⊢ ➡𝐍[h,0] T2 → ❨G,L❩ ⊢ T1 ➡*𝐍[h,n] T2.
/2 width=1 by conj/ qed.

(* Basic forward lemmas *****************************************************)

lemma cpmre_fwd_cpms (h) (n) (G) (L):
      ∀T1,T2. ❨G,L❩ ⊢ T1 ➡*𝐍[h,n] T2 → ❨G,L❩ ⊢ T1 ➡*[h,n] T2.
#h #n #G #L #T1 #T2 * //
qed-.
