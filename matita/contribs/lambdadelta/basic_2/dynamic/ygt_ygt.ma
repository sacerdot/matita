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

include "basic_2/dynamic/ygt.ma".

(* "BIG TREE" ORDER FOR CLOSURES ********************************************)

(* Main properties **********************************************************)

theorem ygt_trans: ∀h,g. tri_transitive … (ygt h g).
/3 width=5 by ygt_fwd_yprs, ygt_yprs_trans/ qed-.
