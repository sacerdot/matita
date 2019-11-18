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

include "static_2/notation/relations/stareqsn_6.ma".
include "static_2/syntax/genv.ma".
include "static_2/static/reqx.ma".

(* SORT-IRRELEVANT EQUIVALENCE FOR CLOSURES ON REFERRED ENTRIES *************)

inductive feqx (G) (L1) (T1): relation3 genv lenv term ≝
| feqx_intro_sn: ∀L2,T2. L1 ≛[T1] L2 → T1 ≛ T2 →
                 feqx G L1 T1 G L2 T2
.

interpretation
   "sort-irrelevant equivalence on referred entries (closure)"
   'StarEqSn G1 L1 T1 G2 L2 T2 = (feqx G1 L1 T1 G2 L2 T2).

(* Basic_properties *********************************************************)

lemma feqx_intro_dx (G): ∀L1,L2,T2. L1 ≛[T2] L2 →
                         ∀T1. T1 ≛ T2 → ⦃G,L1,T1⦄ ≛ ⦃G,L2,T2⦄.
/3 width=3 by feqx_intro_sn, teqx_reqx_div/ qed.

(* Basic inversion lemmas ***************************************************)

lemma feqx_inv_gen_sn: ∀G1,G2,L1,L2,T1,T2. ⦃G1,L1,T1⦄ ≛ ⦃G2,L2,T2⦄ →
                       ∧∧ G1 = G2 & L1 ≛[T1] L2 & T1 ≛ T2.
#G1 #G2 #L1 #L2 #T1 #T2 * -G2 -L2 -T2 /2 width=1 by and3_intro/
qed-.

lemma feqx_inv_gen_dx: ∀G1,G2,L1,L2,T1,T2. ⦃G1,L1,T1⦄ ≛ ⦃G2,L2,T2⦄ →
                       ∧∧ G1 = G2 & L1 ≛[T2] L2 & T1 ≛ T2.
#G1 #G2 #L1 #L2 #T1 #T2 * -G2 -L2 -T2
/3 width=3 by teqx_reqx_conf, and3_intro/
qed-.

(* Basic_2A1: removed theorems 6:
              fleq_refl fleq_sym fleq_inv_gen
              fleq_trans fleq_canc_sn fleq_canc_dx
*)
