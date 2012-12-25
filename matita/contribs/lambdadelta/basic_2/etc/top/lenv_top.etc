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

notation "hvbox( T1 𝟙 break term 46 T2 )"
   non associative with precedence 45
   for @{ 'RTop $T1 $T2 }.

include "basic_2/grammar/lenv_px.ma".

(* POINTWISE EXTENSION OF TOP RELATION FOR TERMS ****************************)

definition ttop: relation term ≝ λT1,T2. True.

definition ltop: relation lenv ≝ lpx ttop.

interpretation
  "top reduction (environment)"
  'RTop L1 L2 = (ltop L1 L2).

(* Basic properties *********************************************************)

lemma ltop_refl: reflexive … ltop.
/2 width=1/ qed.

lemma ltop_sym: symmetric … ltop.
/2 width=1/ qed.

lemma ltop_trans: transitive … ltop.
/2 width=3/ qed.

lemma ltop_append: ∀K1,K2. K1 𝟙 K2 → ∀L1,L2. L1 𝟙 L2 → L1 @@ K1 𝟙 L2 @@ K2.
/2 width=1/ qed.

(* Basic inversion lemmas ***************************************************)

lemma ltop_inv_atom1: ∀L2. ⋆ 𝟙 L2 → L2 = ⋆.
/2 width=2 by lpx_inv_atom1/ qed-.

lemma ltop_inv_pair1: ∀K1,I,V1,L2. K1. ⓑ{I} V1 𝟙 L2 →
                      ∃∃K2,V2. K1 𝟙 K2 & L2 = K2. ⓑ{I} V2.
#K1 #I #V1 #L2 #H
elim (lpx_inv_pair1 … H) -H /2 width=4/
qed-.

lemma ltop_inv_atom2: ∀L1. L1 𝟙 ⋆ → L1 = ⋆.
/2 width=2 by lpx_inv_atom2/ qed-.

lemma ltop_inv_pair2: ∀L1,K2,I,V2. L1 𝟙 K2. ⓑ{I} V2 →
                      ∃∃K1,V1. K1 𝟙 K2 & L1 = K1. ⓑ{I} V1.
#L1 #K2 #I #V2 #H
elim (lpx_inv_pair2 … H) -H /2 width=4/
qed-.

(* Basic forward lemmas *****************************************************)

lemma ltop_fwd_length: ∀L1,L2. L1 𝟙 L2 → |L1| = |L2|.
/2 width=2 by lpx_fwd_length/ qed-.
