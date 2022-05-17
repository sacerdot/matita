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

include "delayed_updating/unwind/unwind_gen.ma".
include "ground/relocation/tr_compose_pap.ma".

(* GENERIC UNWIND FOR PATH **************************************************)

(* Properties with tr_compose ***********************************************)

lemma unwind_gen_after (f2) (f1) (p):
      ◆[f2]◆[f1]p = ◆[λn.(f2 ((f1 n)@❨n❩))∘(f1 n)]p.
#f2 #f1 #p @(path_ind_unwind … p) -p //
#n #_ <unwind_gen_d_empty <unwind_gen_d_empty //
qed.
