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

include "basic_2/conversion/cpc.ma".

(* CONTEXT-SENSITIVE PARALLEL CONVERSION ON TERMS ***************************)

(* Main properties **********************************************************)

theorem cpc_conf: ∀G,L,T0,T1,T2. ⦃G, L⦄ ⊢ T0 ⬌ T1 → ⦃G, L⦄ ⊢ T0 ⬌ T2 →
                  ∃∃T. ⦃G, L⦄ ⊢ T1 ⬌ T & ⦃G, L⦄ ⊢ T2 ⬌ T.
/3 width=3/ qed-.
