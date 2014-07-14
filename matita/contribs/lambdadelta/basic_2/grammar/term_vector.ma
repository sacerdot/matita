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

include "ground_2/lib/list.ma".
include "basic_2/notation/functions/snappls_2.ma".
include "basic_2/grammar/term_simple.ma".

(* TERMS ********************************************************************)

let rec appls Vs T on Vs ≝
  match Vs with
  [ nil        ⇒ T
  | cons hd tl ⇒ ⓐhd. (appls tl T)
  ].

interpretation "application to vector (term)"
   'SnApplStar Vs T = (appls Vs T).

(* properties concerning simple terms ***************************************)

lemma appls_simple: ∀T,Vs.  𝐒⦃T⦄ → 𝐒⦃ⒶVs.T⦄.
#T * //
qed.
