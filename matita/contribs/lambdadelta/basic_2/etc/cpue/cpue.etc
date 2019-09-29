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

include "basic_2/notation/relations/prediteval_5.ma".
include "basic_2/rt_transition/cnu.ma".
include "basic_2/rt_computation/cpms.ma".

(* EVALUATION FOR T-UNBOUND RT-TRANSITION ON TERMS **************************)

definition cpue (h) (G) (L): relation2 term term ≝
           λT1,T2. ∃∃n. ⦃G,L⦄ ⊢ T1 ➡*[n,h] T2 & ⦃G,L⦄ ⊢ ⥲[h] 𝐍⦃T2⦄.

interpretation "evaluation for t-unbound context-sensitive parallel rt-transition (term)"
   'PRedITEval h G L T1 T2 = (cpue h G L T1 T2).
