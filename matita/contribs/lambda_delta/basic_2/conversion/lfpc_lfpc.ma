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

include "basic_2/conversion/lfpc.ma".

(* FOCALIZED PARALLEL CONVERSION ON LOCAL ENVIRONMENTS **********************)

(* Main properties **********************************************************)

theorem lfpc_conf: ∀L0,L1,L2. ⦃L0⦄ ⬌ ⦃L1⦄ → ⦃L0⦄ ⬌ ⦃L2⦄ →
                   ∃∃L. ⦃L1⦄ ⬌ ⦃L⦄ & ⦃L2⦄ ⬌ ⦃L⦄.
/3 width=3/ qed.
