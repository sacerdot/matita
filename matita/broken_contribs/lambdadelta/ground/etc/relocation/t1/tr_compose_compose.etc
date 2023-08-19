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

include "ground/relocation/t1/tr_compose_pap.ma".
include "ground/relocation/t1/tr_compose_tls.ma".
include "ground/relocation/t1/tr_eq.ma".

(* COMPOSITION FOR TOTAL RELOCATION MAPS ************************************)

(* Main constructions *******************************************************)

corec theorem tr_compose_assoc (f3) (f2) (f1):
              (f3 • f2) • f1 ≗ f3 • (f2 • f1).
cases f1 -f1 #p1 #f1
cases tr_compose_unfold cases tr_compose_unfold cases tr_compose_unfold
cases tr_compose_tls
@stream_eq_cons //
qed.
