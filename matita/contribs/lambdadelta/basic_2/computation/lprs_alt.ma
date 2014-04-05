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

include "basic_2/notation/relations/predsnstaralt_3.ma".
include "basic_2/computation/cprs_cprs.ma".
include "basic_2/computation/lprs.ma".

(* SN PARALLEL COMPUTATION ON LOCAL ENVIRONMENTS ****************************)

(* alternative definition *)
definition lprsa: relation3 genv lenv lenv ≝
           λG. lpx_sn … (cprs G).

interpretation "parallel computation (local environment, sn variant) alternative"
   'PRedSnStarAlt G L1 L2 = (lprsa G L1 L2).

(* Main properties on the alternative definition ****************************)

theorem lprsa_lprs: ∀G,L1,L2. ⦃G, L1⦄ ⊢ ➡➡* L2 → ⦃G, L1⦄ ⊢ ➡* L2.
/2 width=1 by lpx_sn_LTC_TC_lpx_sn/ qed-.

(* Main inversion lemmas on the alternative definition **********************)

theorem lprs_inv_lprsa: ∀G,L1,L2. ⦃G, L1⦄ ⊢ ➡* L2 → ⦃G, L1⦄ ⊢ ➡➡* L2.
/3 width=3 by TC_lpx_sn_inv_lpx_sn_LTC, lpr_cprs_trans/ qed-.

(* Alternative eliminators **************************************************)

lemma lprs_ind_alt: ∀G. ∀R:relation lenv.
                    R (⋆) (⋆) → (
                       ∀I,K1,K2,V1,V2.
                       ⦃G, K1⦄ ⊢ ➡* K2 → ⦃G, K1⦄ ⊢ V1 ➡* V2 →
                       R K1 K2 → R (K1.ⓑ{I}V1) (K2.ⓑ{I}V2)
                    ) →
                    ∀L1,L2. ⦃G, L1⦄ ⊢ ➡* L2 → R L1 L2.
/3 width=4 by TC_lpx_sn_ind, lpr_cprs_trans/ qed-.
