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

include "ground/lib/star.ma".
include "basic_2/notation/relations/predsubtystar_6.ma".
include "basic_2/rt_transition/fpb.ma".

(* PARALLEL RST-COMPUTATION FOR CLOSURES ************************************)

definition fpbs: tri_relation genv lenv term ≝
           tri_TC … fpb.

interpretation
  "parallel rst-computation (closure)"
  'PRedSubTyStar  G1 L1 T1 G2 L2 T2 = (fpbs G1 L1 T1 G2 L2 T2).


(* Basic properties *********************************************************)

(* Basic_2A1: uses: fpbq_fpbs *)
lemma fpb_fpbs:
      ∀G1,G2,L1,L2,T1,T2. ❪G1,L1,T1❫ ≽ ❪G2,L2,T2❫ →
      ❪G1,L1,T1❫ ≥ ❪G2,L2,T2❫.
/2 width=1 by tri_inj/ qed.

lemma fpbs_strap1:
      ∀G1,G,G2,L1,L,L2,T1,T,T2. ❪G1,L1,T1❫ ≥ ❪G,L,T❫ →
      ❪G,L,T❫ ≽ ❪G2,L2,T2❫ → ❪G1,L1,T1❫ ≥ ❪G2,L2,T2❫.
/2 width=5 by tri_step/ qed-.

lemma fpbs_strap2:
      ∀G1,G,G2,L1,L,L2,T1,T,T2. ❪G1,L1,T1❫ ≽ ❪G,L,T❫ →
      ❪G,L,T❫ ≥ ❪G2,L2,T2❫ → ❪G1,L1,T1❫ ≥ ❪G2,L2,T2❫.
/2 width=5 by tri_TC_strap/ qed-.

(* Basic_2A1: removed theorems 3:
              fpb_fpbsa_trans fpbs_fpbsa fpbsa_inv_fpbs
*)
