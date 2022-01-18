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

(* PROTOTERM ****************************************************************)

(* Note: a prototerm is a subset of complete paths *)
definition prototerm: Type[0] ≝ 𝒫❨path❩.

definition prototerm_grafted: path → prototerm → prototerm ≝
           λp,t,q. p●q ϵ t.

interpretation
  "grafted (prototerm)"
  'Pitchfork t p = (prototerm_grafted p t).

definition prototerm_root: prototerm → prototerm ≝
           λt,q. ∃r. q●r ϵ t.

interpretation
  "root (prototerm)"
  'UpTriangle t = (prototerm_root t).

(* Basic constructions ******************************************************)

lemma prototerm_in_comp_root (p) (t):
      p ϵ t → p ϵ ▵t.
/2 width=2 by ex_intro/
qed.
