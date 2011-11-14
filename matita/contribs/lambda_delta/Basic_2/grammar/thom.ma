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

include "Basic_2/grammar/term_simple.ma".

(* HOMOMORPHIC TERMS ********************************************************)

inductive thom: relation term ≝
   | thom_atom: ∀I. thom (𝕒{I}) (𝕒{I})
   | thom_abst: ∀V1,V2,T1,T2. thom (𝕔{Abst} V1. T1) (𝕔{Abst} V2. T2)
   | thom_appl: ∀V1,V2,T1,T2. thom T1 T2 → 𝕊[T1] → 𝕊[T2] →
                thom (𝕔{Appl} V1. T1) (𝕔{Appl} V2. T2)
.

interpretation "homomorphic (term)" 'napart T1 T2 = (thom T1 T2).

(* Basic properties *********************************************************)

lemma thom_sym: ∀T1,T2. T1 ≈ T2 → T2 ≈ T1.
#T1 #T2 #H elim H -H T1 T2 /2/
qed.

lemma thom_refl2: ∀T1,T2. T1 ≈ T2 → T2 ≈ T2.
#T1 #T2 #H elim H -H T1 T2 /2/
qed.

lemma thom_refl1: ∀T1,T2. T1 ≈ T2 → T1 ≈ T1.
/3/ qed.

lemma simple_thom_repl_dx: ∀T1,T2. T1 ≈ T2 → 𝕊[T1] → 𝕊[T2].
#T1 #T2 #H elim H -H T1 T2 //
#V1 #V2 #T1 #T2 #H
elim (simple_inv_bind … H)
qed. (**) (* remove from index *)

lemma simple_thom_repl_sn: ∀T1,T2. T1 ≈ T2 → 𝕊[T2] → 𝕊[T1].
/3/ qed-.

(* Basic inversion lemmas ***************************************************)


(* Basic_1: removed theorems 7:
            iso_gen_sort iso_gen_lref iso_gen_head iso_refl iso_trans
            iso_flats_lref_bind_false iso_flats_flat_bind_false
*)
