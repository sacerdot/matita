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

include "ground/lib/subset.ma".
include "delayed_updating/syntax/path.ma".
include "delayed_updating/notation/functions/pitchfork_2.ma".
include "delayed_updating/notation/functions/uptriangle_1.ma".

(* PRETERM ******************************************************************)

(* Note: preterms are subsets of complete paths *)
definition preterm: Type[0] ≝ 𝒫❨path❩.

definition preterm_grafted: path → preterm → preterm ≝
           λp,t,q. p●q ϵ t.

interpretation
  "grafted (preterm)"
  'Pitchfork t p = (preterm_grafted p t).

definition preterm_root: preterm → preterm ≝
           λt,q. ∃r. q●r ϵ t.

interpretation
  "root (preterm)"
  'UpTriangle t = (preterm_root t).

(* Basic constructions ******************************************************)

lemma preterm_in_comp_root (p) (t):
      p ϵ t → p ϵ ▵t.
/2 width=2 by ex_intro/
qed.
