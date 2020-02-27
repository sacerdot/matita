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

include "ground_2/notation/functions/append_2.ma".
include "ground_2/relocation/mr2.ma".

(* MULTIPLE RELOCATION WITH PAIRS *******************************************)

let rec mr2_append cs1 cs2 on cs1 ≝ 
  match cs1 with
  [ nil2          ⇒ cs2
  | cons2 l m cs1 ⇒ ❨l, m❩; mr2_append cs1 cs2
  ].

interpretation "append (multiple relocation with pairs)" 
  'Append cs1 cs2 = (mr2_append cs1 cs2).

(* Basic properties *********************************************************)

lemma mr2_append_nil (cs2): cs2 = ◊ @@ cs2.
// qed.

lemma mr2_append_cons (l) (m) (cs1) (cs2):
      ❨l, m❩; (cs1 @@ cs2) = (❨l, m❩; cs1) @@ cs2.
// qed.
