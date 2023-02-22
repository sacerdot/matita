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

include "static_2/static/reqg_fqup.ma".
include "static_2/static/feqg.ma".

(* GENERIC EQUIVALENCE FOR CLOSURES ON REFERRED ENTRIES *********************)

(* Properties with generic equivalence for terms ****************************)

lemma teqg_feqg (S):
      reflexive … S →
      ∀T1,T2. T1 ≛[S] T2 →
      ∀G,L. ❨G,L,T1❩ ≛[S] ❨G,L,T2❩.
/3 width=1 by feqg_intro_sn, reqg_refl/ qed.

(* Advanced properties ******************************************************)

lemma feqg_refl (S):
      reflexive … S →
      tri_reflexive … (feqg S).
/3 width=1 by teqg_refl, teqg_feqg/ qed.
