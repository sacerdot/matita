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

include "ground/xoa/ex_3_6.ma".
include "basic_2/notation/relations/predsubtystarproper_6.ma".
include "basic_2/rt_transition/fpbc.ma".
include "basic_2/rt_computation/fpbs.ma".

(* PROPER PARALLEL RST-COMPUTATION FOR CLOSURES *****************************)

definition fpbg: tri_relation genv lenv term ≝
           λG1,L1,T1,G2,L2,T2.
           ∃∃G3,L3,T3,G4,L4,T4. ❪G1,L1,T1❫ ≥ ❪G3,L3,T3❫ & ❪G3,L3,T3❫ ≻ ❪G4,L4,T4❫ & ❪G4,L4,T4❫ ≥ ❪G2,L2,T2❫.

interpretation
  "proper parallel rst-computation (closure)"
  'PRedSubTyStarProper G1 L1 T1 G2 L2 T2 = (fpbg G1 L1 T1 G2 L2 T2).

(* Basic inversion lemmas ***************************************************)

lemma fpbg_inv_gen (G1) (G2) (L1) (L2) (T1) (T2):
      ❪G1,L1,T1❫ > ❪G2,L2,T2❫ →
      ∃∃G3,L3,T3,G4,L4,T4. ❪G1,L1,T1❫ ≥ ❪G3,L3,T3❫ & ❪G3,L3,T3❫ ≻ ❪G4,L4,T4❫ & ❪G4,L4,T4❫ ≥ ❪G2,L2,T2❫.
// qed-.

(* Basic properties *********************************************************)

lemma fpbg_intro (G3) (G4) (L3) (L4) (T3) (T4):
      ∀G1,L1,T1,G2,L2,T2.
      ❪G1,L1,T1❫ ≥ ❪G3,L3,T3❫ → ❪G3,L3,T3❫ ≻ ❪G4,L4,T4❫ →
      ❪G4,L4,T4❫ ≥ ❪G2,L2,T2❫ → ❪G1,L1,T1❫ > ❪G2,L2,T2❫.
/2 width=9 by ex3_6_intro/ qed.

(* Basic_2A1: was: fpbg_fpbq_trans *)
lemma fpbg_fpb_trans:
      ∀G1,G,G2,L1,L,L2,T1,T,T2.
      ❪G1,L1,T1❫ > ❪G,L,T❫ → ❪G,L,T❫ ≽ ❪G2,L2,T2❫ →
      ❪G1,L1,T1❫ > ❪G2,L2,T2❫.
#G1 #G #G2 #L1 #L #L2 #T1 #T #T2 #H1 #H2
elim (fpbg_inv_gen … H1) -H1
/3 width=13 by fpbs_strap1, fpbg_intro/
qed-.

(* Basic_2A1: was: fpbq_fpbg_trans *)
lemma fpb_fpbg_trans:
      ∀G1,G,G2,L1,L,L2,T1,T,T2.
      ❪G1,L1,T1❫ ≽ ❪G,L,T❫ → ❪G,L,T❫ > ❪G2,L2,T2❫ →
      ❪G1,L1,T1❫ > ❪G2,L2,T2❫.
#G1 #G #G2 #L1 #L #L2 #T1 #T #T2 #H1 #H2
elim (fpbg_inv_gen … H2) -H2
/3 width=13 by fpbs_strap2, fpbg_intro/
qed-.
