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

include "basic_2/i_static/tc_lfxs_tc_lfxs.ma".
include "basic_2/rt_computation/lfpxs.ma".

(* UNBOUND PARALLEL RT-COMPUTATION FOR LOCAL ENV.S ON REFERRED ENTRIES ******)

(* Main properties **********************************************************)

(* Basic_2A1: uses: lpxs_trans *)
theorem lfpxs_trans: ∀h,G,T. Transitive … (lfpxs h G T).
/2 width=3 by tc_lfxs_trans/ qed-.
