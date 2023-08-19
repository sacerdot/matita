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

include "ground/relocation/t1/tr_compose.ma".
include "ground/relocation/t1/tr_pap_eq.ma".
include "ground/lib/stream_tls_eq.ma".

(* COMPOSITION FOR TOTAL RELOCATION MAPS ************************************)

(* Constructions with stream_eq *********************************************)

corec lemma tr_compose_eq_repl (f2) (g2):
            f2 ≗ g2 → stream_eq_repl … (λf1,g1. f2•f1 ≗ g2•g1).
#Hfg2 * #p1 #f1 * #q1 #g1 #H
cases (stream_eq_inv_cons_bi … H) -H [|*: // ] * #Hfg1 -q1
cases tr_compose_unfold cases tr_compose_unfold
/5 width=1 by tr_pap_eq_repl, stream_tls_eq_repl, stream_eq_cons/
qed.
