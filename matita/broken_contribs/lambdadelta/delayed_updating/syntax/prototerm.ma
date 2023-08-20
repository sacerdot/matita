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
           λt,q. ∃r. r ϵ t⋔q.

interpretation
  "root (prototerm)"
  'UpTriangle t = (prototerm_root t).

definition pt_append (p) (t): prototerm ≝
           λr. ∃∃q. q ϵ t & p●q = r.

interpretation
  "append (prototerm)"
  'BlackCircle p t = (pt_append p t).

(* Basic inversions *********************************************************)

lemma prototerm_grafted_inv_gen (t) (p) (q):
      q ϵ t⋔p → p●q ϵ t.
// qed-.

(* Basic constructions ******************************************************)

lemma prototerm_in_comp_root (p) (t):
      p ϵ t → p ϵ ▵t.
/2 width=2 by ex_intro/
qed.

lemma pt_append_in (p) (q) (t):
      q ϵ t → p●q ϵ p●t.
/2 width=3 by ex2_intro/
qed.

(* Basic destructions *******************************************************)

lemma prototerm_in_root_append_des_sn (t) (p) (q):
      p●q ϵ ▵t → p ϵ ▵t.
#t #p #q * #r #Hr
/2 width=2 by ex_intro/
qed-.
