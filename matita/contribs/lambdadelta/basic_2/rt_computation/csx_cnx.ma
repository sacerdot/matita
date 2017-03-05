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

(* STRONGLY NORMALIZING TERMS FOR UNCOUNTED PARALLEL RT-TRANSITION **********)

include "basic_2/rt_transition/cnx.ma".
include "basic_2/rt_computation/csx.ma".

(* Properties with normal terms for uncounted parallel rt-transition ********)

(* Basic_1: was just: sn3_nf2 *)
lemma cnx_csx: ∀h,o,G,L,T. ⦃G, L⦄ ⊢ ⬈[h, o] 𝐍⦃T⦄ → ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃T⦄.
/2 width=1 by NF_to_SN/ qed.
