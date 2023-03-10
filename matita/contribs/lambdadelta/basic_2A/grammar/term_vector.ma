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
include "basic_2A/notation/functions/snapplvector_2.ma".
include "basic_2A/grammar/term_simple.ma".

(* TERMS ********************************************************************)

let rec applv Vs T on Vs ≝
  match Vs with
  [ nil        ⇒ T
  | cons hd tl ⇒ ⓐhd. (applv tl T)
  ].

interpretation "application to vector (term)"
   'SnApplVector Vs T = (applv Vs T).

(* properties concerning simple terms ***************************************)

lemma applv_simple: ∀T,Vs.  𝐒⦃T⦄ → 𝐒⦃ⒶVs.T⦄.
#T * //
qed.
