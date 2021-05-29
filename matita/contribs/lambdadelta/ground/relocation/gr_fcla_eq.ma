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

include "ground/relocation/gr_isi_eq.ma".
include "ground/relocation/gr_fcla.ma".

(* FINITE COLENGTH ASSIGNMENT FOR GENERIC RELOCATION MAPS *******************)

(* Constructions with gr_eq *************************************************)

(*** fcla_eq_repl_back *)
lemma gr_fcla_eq_repl_back (n):
      gr_eq_repl_back … (λf. 𝐂❪f❫ ≘ n).
#n #f1 #H elim H -f1 -n /3 width=3 by gr_fcla_isi, gr_isi_eq_repl_back/
#f1 #n #_ #IH #g2 #H [ elim (gr_eq_inv_push_sn … H) | elim (gr_eq_inv_next_sn … H) ] -H
/3 width=3 by gr_fcla_push, gr_fcla_next/
qed-.

(*** fcla_eq_repl_fwd *)
lemma fcla_eq_repl_fwd (n):
      gr_eq_repl_fwd … (λf. 𝐂❪f❫ ≘ n).
#n @gr_eq_repl_sym /2 width=3 by gr_fcla_eq_repl_back/
qed-.
