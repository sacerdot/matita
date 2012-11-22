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

include "basic_2/conversion/fpc.ma".

(* CONTEXT-FREE PARALLEL CONVERSION ON CLOSURES *****************************)

(* Main properties **********************************************************)

theorem fpc_conf: ∀L0,L1,T0,T1. ⦃L0, T0⦄ ⬌ ⦃L1, T1⦄ →
                  ∀L2,T2. ⦃L0, T0⦄ ⬌ ⦃L2, T2⦄ →
                  ∃∃L,T. ⦃L1, T1⦄ ⬌ ⦃L, T⦄ & ⦃L2, T2⦄ ⬌ ⦃L, T⦄.
/3 width=4/ qed.
