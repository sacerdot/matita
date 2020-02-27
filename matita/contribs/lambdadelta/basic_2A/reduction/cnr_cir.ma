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

include "basic_2A/reduction/cpr_cir.ma".
include "basic_2A/reduction/cnr_crr.ma".

(* NORMAL TERMS FOR CONTEXT-SENSITIVE REDUCTION *****************************)

(* Main properties on irreducibility ****************************************)

theorem cir_cnr: ∀G,L,T. ⦃G, L⦄ ⊢ ➡ 𝐈⦃T⦄ → ⦃G, L⦄ ⊢ ➡ 𝐍⦃T⦄.
/3 width=4 by cpr_fwd_cir, sym_eq/ qed.

(* Main inversion lemmas on irreducibility **********************************)

theorem cnr_inv_cir: ∀G,L,T. ⦃G, L⦄ ⊢ ➡ 𝐍⦃T⦄ → ⦃G, L⦄ ⊢ ➡ 𝐈⦃T⦄.
/2 width=5 by cnr_inv_crr/ qed-.
