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

include "explicit_updating/syntax/unwind_eq.ma".
include "explicit_updating/syntax/beta_eq.ma".
include "explicit_updating/notation/functions/solidi_beta_1.ma".

(* MARKED β-STEP FOR P-REDUCTION ********************************************)

definition pbeta1 (b): relation6 (𝕋) (𝕋) (𝕋) (𝕋 ) (𝕋) (𝕋) ≝
           λv1,v2,t1,t2,x,y.
           ∧∧ ＠v1.𝛌b.t1 ≐ ▼[𝐢]x & ⬕[𝟎←v2]t2 ≐ y.

interpretation
  "marked β-step (p-reduction)"
  'SolidiBeta b = (pbeta1 b).
