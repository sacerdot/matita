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

include "Basic_2/unfold/tpss_lift.ma".
include "Basic_2/reduction/tpr_lift.ma".
include "Basic_2/reduction/cpr.ma".

(* CONTEXT-SENSITIVE PARALLEL REDUCTION ON TERMS ****************************)

(* Advanced properties ******************************************************)

lemma cpr_delta: ∀L,K,V1,W1,W2,i.
                 ↓[0, i] L ≡ K. 𝕓{Abbr} V1 → K ⊢ V1 [0, |L| - i - 1] ≫* W1 →
                 ↑[0, i + 1] W1 ≡ W2 → L ⊢ #i ⇒ W2.
#L #K #V1 #W1 #W2 #i #HLK #HVW1 #HW12
@ex2_1_intro [2: // | skip | @tpss_subst /2 width=6/ ] (**) (* /4 width=6/ is too slow *)
qed.

(* Advanced inversion lemmas ************************************************)

(* Basic_1: was: pr2_gen_lref *)
lemma cpr_inv_lref1: ∀L,T2,i. L ⊢ #i ⇒ T2 →
                     T2 = #i ∨
                     ∃∃K,V1,T1. ↓[0, i] L ≡ K. 𝕓{Abbr} V1 &
                                K ⊢ V1 [0, |L| - i - 1] ≫* T1 &
                                ↑[0, i + 1] T1 ≡ T2 &
                                i < |L|.
#L #T2 #i * #X #H
>(tpr_inv_atom1 … H) -H #H
elim (tpss_inv_lref1 … H) -H /2/
* /3 width=6/
qed.

(* Basic_1: was: pr2_gen_abst *)
lemma cpr_inv_abst1: ∀V1,T1,U2. 𝕔{Abst} V1. T1 ⇒ U2 →
                     ∃∃V2,T2. V1 ⇒ V2 & T1 ⇒ T2 & U2 = 𝕔{Abst} V2. T2.
/2/ qed.

(* Relocation properties ****************************************************)

(* Basic_1: was: pr2_lift *)

(* Basic_1: was: pr2_gen_lift *)

