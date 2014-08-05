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

include "basic_2/reduction/cpx_cix.ma".
include "basic_2/reduction/cnx_crx.ma".

(* NORMAL TERMS FOR CONTEXT-SENSITIVE EXTENDED REDUCTION ********************)

(* Main properties on irreducibility ****************************************)

theorem cix_cnx: ∀h,g,G,L,T. ⦃G, L⦄ ⊢ ➡[h, g] 𝐈⦃T⦄ → ⦃G, L⦄ ⊢ ➡[h, g] 𝐍⦃T⦄.
/2 width=6 by cpx_fwd_cix/ qed.

(* Main inversion lemmas on irreducibility **********************************)

theorem cnx_inv_cix: ∀h,g,G,L,T. ⦃G, L⦄ ⊢ ➡[h, g] 𝐍⦃T⦄ → ⦃G, L⦄ ⊢ ➡[h, g] 𝐈⦃T⦄.
/2 width=7 by cnx_inv_crx/ qed-.
