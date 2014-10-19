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

include "basic_2/computation/fsb_aaa.ma".
include "basic_2/dynamic/snv_aaa.ma".

(* STRATIFIED NATIVE VALIDITY FOR TERMS *************************************)

(* forward lemmas on "qrst" strongly normalizing closures *********************)

lemma snv_fwd_fsb: ∀h,g,G,L,T. ⦃G, L⦄ ⊢ T ¡[h, g] → ⦥[h, g] ⦃G, L, T⦄.
#h #g #G #L #T #H elim (snv_fwd_aaa … H) -H /2 width=2 by aaa_fsb/
qed-.
