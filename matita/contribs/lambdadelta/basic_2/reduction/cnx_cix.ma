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

(* CONTEXT-SENSITIVE EXTENDED NORMAL TERMS **********************************)

(* Main properties on context-sensitive extended irreducible terms **********)

theorem cix_cnr: ∀h,g,G,L,T. ⦃G, L⦄ ⊢ 𝐈[h, g]⦃T⦄ → ⦃G, L⦄ ⊢ 𝐍[h, g]⦃T⦄.
/2 width=6 by cpx_fwd_cix/ qed.

(* Main inversion lemmas on context-sensitive extended irreducible terms ****)

theorem cnr_inv_cix: ∀h,g,G,L,T. ⦃G, L⦄ ⊢ 𝐍[h, g]⦃T⦄ → ⦃G, L⦄ ⊢ 𝐈[h, g]⦃T⦄.
/2 width=7 by cnx_inv_crx/ qed-.
