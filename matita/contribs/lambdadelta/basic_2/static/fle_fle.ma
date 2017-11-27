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

include "basic_2/static/frees_frees.ma".
include "basic_2/static/fle.ma".

(* FREE VARIABLES INCLUSION FOR RESTRICTED CLOSURES *************************)

(* Main properties **********************************************************)

theorem fle_trans: bi_transitive … fle.
#L1 #L #T1 #T * #f1 #f #HT1 #HT #Hf1 #L2 #T2 * #g #f2 #Hg #HT2 #Hf2
/5 width=8 by frees_mono, sle_trans, sle_eq_repl_back2, ex3_2_intro/
qed-.
