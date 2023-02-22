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

include "static_2/syntax/teq.ma".

(* SYNTACTIC EQUIVALENCE ON TERMS *******************************************)

(* Main forward properties **************************************************)

theorem teq_trans:
        Transitive … teq.
/2 width=3 by teq_repl_1/ qed-.
(*
theorem teq_repl_2 (R):
        replace_2 … R teq teq.
#R #T1 #U1 #HTU1 #T2 #HT12 #U2 #HU12
<(teq_inv_eq … HT12) -T2 <(teq_inv_eq … HU12) -U2 //
qed-.
*)
