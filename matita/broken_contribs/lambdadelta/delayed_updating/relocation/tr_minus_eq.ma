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

include "delayed_updating/relocation/tr_minus.ma".
include "ground/lib/stream_eq.ma".

(* RIGHT SUBTRACTION FOR TOTAL RELOCATION MAPS ******************************)

(* Constructions with tr_eq *************************************************)

corec lemma tr_minus_eq_repl (n):
            stream_eq_repl … (λf1,f2. f1-n ≗ f2-n).
cases n -n
[ #f1 #f2 #Hf -tr_minus_eq_repl //
| #q * #p1 #f1 * #p2 #f2 #Hf
  cases (stream_eq_inv_cons_bi … Hf) -Hf  [|*: // ] * #Hf -p2
  cases tr_minus_cons_inj cases tr_minus_cons_inj
  @stream_eq_cons //
  @tr_minus_eq_repl //
]
qed.
