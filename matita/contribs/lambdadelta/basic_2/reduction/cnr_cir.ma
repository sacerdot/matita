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

include "basic_2/reduction/cpr_cir.ma".
include "basic_2/reduction/cnr_crr.ma".

(* CONTEXT-SENSITIVE NORMAL TERMS *******************************************)

(* Main properties on context-sensitive irreducible terms *******************)

theorem cir_cnr: ∀L,T. ⦃G, L⦄ ⊢ 𝐈⦃T⦄ → ⦃G, L⦄ ⊢ 𝐍⦃T⦄.
/2 width=3 by cpr_fwd_cir/ qed.

(* Main inversion lemmas on context-sensitive irreducible terms *************)

theorem cnr_inv_cir: ∀L,T. ⦃G, L⦄ ⊢ 𝐍⦃T⦄ → ⦃G, L⦄ ⊢ 𝐈⦃T⦄.
/2 width=4 by cnr_inv_crr/ qed-.
