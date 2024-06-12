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

include "ground/xoa/ex_2_3.ma".
include "delayed_updating/syntax/preterm.ma".
include "delayed_updating/computation/dbfrs.ma".

(* DELAYED BALANCED FOCUSED COMPUTATION *************************************)

(* Confluence ***************************************************************)

axiom dbfrs_conf (t0):
      t0 ϵ 𝐓 → ∀t1,rs1. t0 ➡*𝐝𝐛𝐟[rs1] t1 → ∀t2,rs2. t0 ➡*𝐝𝐛𝐟[rs2] t2 →
      ∃∃t,ss1,ss2. t1 ➡*𝐝𝐛𝐟[ss1] t & t2 ➡*𝐝𝐛𝐟[ss2] t.
