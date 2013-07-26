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

include "basic_2/notation/relations/predsnstaralt_4.ma".
include "basic_2/computation/cpxs_cpxs.ma".
include "basic_2/computation/lpxs.ma".

(* SN EXTENDED PARALLEL COMPUTATION ON LOCAL ENVIRONMENTS *******************)

(* alternative definition *)
definition lpxsa: ∀h. sd h → relation lenv ≝ λh,g. lpx_sn … (cpxs h g).

interpretation "extended parallel computation (local environment, sn variant) alternative"
   'PRedSnStarAlt h g L1 L2 = (lpxsa h g L1 L2).

(* Main properties on the alternative definition ****************************)

theorem lpxsa_lpxs: ∀h,g,L1,L2. ⦃h, L1⦄ ⊢ ➡➡*[g] L2 → ⦃h, L1⦄ ⊢ ➡*[g] L2.
/2 width=1 by lpx_sn_LTC_TC_lpx_sn/ qed-.

(* Main inversion lemmas on the alternative definition **********************)

theorem lpxs_inv_lpxsa: ∀h,g,L1,L2. ⦃h, L1⦄ ⊢ ➡*[g] L2 → ⦃h, L1⦄ ⊢ ➡➡*[g] L2.
/3 width=3 by TC_lpx_sn_inv_lpx_sn_LTC, lpx_cpxs_trans/ qed-.

(* Alternative eliminators **************************************************)

lemma lpxs_ind_alt: ∀h,g. ∀R:relation lenv.
                    R (⋆) (⋆) → (
                       ∀I,K1,K2,V1,V2.
                       ⦃h, K1⦄ ⊢ ➡*[g] K2 → ⦃h, K1⦄ ⊢ V1 ➡*[g] V2 →
                       R K1 K2 → R (K1.ⓑ{I}V1) (K2.ⓑ{I}V2)
                    ) →
                    ∀L1,L2. ⦃h, L1⦄ ⊢ ➡*[g] L2 → R L1 L2.
/3 width=4 by TC_lpx_sn_ind, lpx_cpxs_trans/ qed-.
