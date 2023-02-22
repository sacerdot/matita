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

include "ground/relocation/tr_eq.ma".
include "ground/relocation/tr_pn.ma".

(* PUSH AND NEXT FOR TOTAL RELOCATION MAPS **********************************)

(* Constructions with stream_eq *********************************************)

lemma tr_push_eq_repl:
      stream_eq_repl … (λf1,f2. ⫯f1 ≗ ⫯f2).
/2 width=1 by stream_eq_cons/ qed.

lemma tr_next_eq_repl:
      stream_eq_repl … (λf1,f2. ↑f1 ≗ ↑f2).
* #p1 #f1 * #p2 #f2 #H
elim (stream_eq_inv_cons_bi … H) -H [|*: // ]
/2 width=1 by stream_eq_cons/
qed.
