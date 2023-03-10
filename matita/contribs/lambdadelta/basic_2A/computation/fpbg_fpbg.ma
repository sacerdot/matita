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

include "basic_2A/computation/fpbg_fpbs.ma".

(* "QRST" PROPER PARALLEL COMPUTATION FOR CLOSURES **************************)

(* Main properties **********************************************************)

theorem fpbg_trans: ∀h,g. tri_transitive … (fpbg h g).
/3 width=5 by fpbg_fpbs_trans, fpbg_fwd_fpbs/ qed-.
