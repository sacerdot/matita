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

include "basic_2/unfold/ltpss.ma".

(* BASIC LOCAL ENVIRONMENT THINNING *****************************************)

definition thin: nat → nat → relation lenv ≝
                 λd,e,L1,L2. ∃∃L. L1 ▶* [d, e] L & ⇩[d, e] L ≡ L2.

interpretation "basic thinning (local environment)"
   'TSubst L1 d e L2 = (thin d e L1 L2).

(* Basic properties *********************************************************)

lemma ldrop_thin: ∀L1,L2,d,e. ⇩[d, e] L1 ≡ L2 → L1 [d, e] ≡ L2.
/2 width=3/ qed.

(* Basic inversion lemmas ***************************************************)

lemma thin_inv_thin1: ∀I,K1,V1,L2,e. K1. ⓑ{I} V1 [0, e] ≡ L2 → 0 < e →
                      K1 [0, e - 1] ≡ L2.
#I #K1 #V1 #L2 #e * #X #HK1 #HL2 #e
elim (ltpss_inv_tpss21 … HK1 ?) -HK1 // #K #V #HK1 #_ #H destruct
lapply (ldrop_inv_ldrop1 … HL2 ?) -HL2 // /2 width=3/
qed-.
