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

include "ground/lib/list.ma".
include "static_2/notation/functions/snapplvector_2.ma".
include "static_2/syntax/term_simple.ma".

(* TERMS ********************************************************************)

rec definition applv Vs T on Vs ≝
match Vs with
[ list_empty       ⇒ T
| list_lcons hd tl ⇒ ⓐhd. (applv tl T)
].

interpretation "application to vector (term)"
   'SnApplVector Vs T = (applv Vs T).

(* Basic properties *********************************************************)

lemma applv_empty: ∀T. Ⓐⓔ.T = T.
// qed.

lemma applv_lcons: ∀V,Vs,T. ⒶV⨮Vs.T = ⓐV.ⒶVs.T.
// qed.

(* Properties with simple terms *********************************************)

lemma applv_simple: ∀T,Vs. 𝐒❨T❩ → 𝐒❨ⒶVs.T❩.
#T * //
qed.
