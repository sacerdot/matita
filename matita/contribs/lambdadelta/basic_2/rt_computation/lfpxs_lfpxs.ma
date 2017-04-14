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

include "basic_2/rt_computation/lfpxs.ma".

(* UNCOUNTED PARALLEL RT-COMPUTATION FOR LOCAL ENV.S ON REFERRED ENTRIES ****)

(* Main properties **********************************************************)

(* Basic_2A1: uses: lpxs_trans *)
theorem lfpxs_trans: ∀h,G,T. Transitive … (lfpxs h G T).
#h #G #T #L1 #L #HL1 #L2 #HL2 @(trans_TC … HL1 HL2) (**) (* auto fails *) 
qed-.
