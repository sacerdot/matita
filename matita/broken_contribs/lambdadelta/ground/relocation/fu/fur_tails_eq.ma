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

include "ground/relocation/fu/fur_tails_xapp.ma".
include "ground/relocation/fu/fur_xapp_eq.ma".

(* ITERATED TAIL FOR FINITE RELOCATION MAPS FOR UNWIND **********************)

(* Constructions with fur_eq ************************************************)

lemma fur_tails_eq_repl (n):
      compatible_2_fwd … fur_eq fur_eq (λf.⫰*[n]f).
#n #f1 #f2 #Hf
@fur_eq_xapp #n
<fur_xapp_tails <fur_xapp_tails
<(fur_xapp_eq_repl … Hf) <(fur_xapp_eq_repl … Hf) -Hf //
qed.
