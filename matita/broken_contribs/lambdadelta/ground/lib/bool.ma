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

include "basics/bool.ma".
include "ground/notation/functions/no_0.ma".
include "ground/notation/functions/yes_0.ma".
include "ground/lib/relations.ma".

(* BOOLEANS *****************************************************************)

interpretation
  "false (booleans)"
  'no = false.

interpretation
  "true (booleans)"
  'yes = true.

(* Advanced constructions ***************************************************)

lemma eq_bool_dec (b1:bool) (b2:bool):
      Decidable (b1 = b2).
* * /2 width=1 by or_introl/
@or_intror #H destruct
qed-.
