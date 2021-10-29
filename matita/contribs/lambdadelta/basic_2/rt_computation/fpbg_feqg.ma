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

include "basic_2/rt_computation/fpbs_fpbc.ma".
include "basic_2/rt_computation/fpbg_fpbs.ma".

(* PROPER PARALLEL RST-COMPUTATION FOR CLOSURES *****************************)

(* Properties with generic equivalence for closures *************************)

(* Basic_2A1: uses: fpbg_fleq_trans *)
lemma fpbg_feqg_trans (S) (G) (L) (T):
      reflexive … S → symmetric … S →
      ∀G1,L1,T1. ❨G1,L1,T1❩ > ❨G,L,T❩ →
      ∀G2,L2,T2. ❨G,L,T❩ ≛[S] ❨G2,L2,T2❩ → ❨G1,L1,T1❩ > ❨G2,L2,T2❩.
/3 width=8 by fpbg_fpb_trans, feqg_fpb/ qed-.

(* Basic_2A1: uses: fleq_fpbg_trans *)
lemma feqg_fpbg_trans (S) (G) (L) (T):
      reflexive … S → symmetric … S →
      ∀G1,L1,T1. ❨G1,L1,T1❩ ≛[S] ❨G,L,T❩ →
      ∀G2,L2,T2. ❨G,L,T❩ > ❨G2,L2,T2❩ → ❨G1,L1,T1❩ > ❨G2,L2,T2❩.
/3 width=8 by fpb_fpbg_trans, feqg_fpb/ qed-.

(* Properties with generic equivalence for terms ****************************)

lemma fpbg_teqg_div (S):
      reflexive … S → symmetric … S →
      ∀G1,G2,L1,L2,T1,T. ❨G1,L1,T1❩ > ❨G2,L2,T❩ →
      ∀T2. T2 ≛[S] T → ❨G1,L1,T1❩ > ❨G2,L2,T2❩.
/4 width=8 by fpbg_feqg_trans, teqg_feqg, teqg_sym/ qed-.

(* Advanced inversion lemmas of parallel rst-computation on closures ********)

(* Basic_2A1: was: fpbs_fpbg *)
lemma fpbs_inv_fpbg:
      ∀G1,G2,L1,L2,T1,T2. ❨G1,L1,T1❩ ≥ ❨G2,L2,T2❩ →
      ∨∨ ❨G1,L1,T1❩ ≅ ❨G2,L2,T2❩
       | ❨G1,L1,T1❩ > ❨G2,L2,T2❩.
#G1 #G2 #L1 #L2 #T1 #T2 #H
elim (fpbs_inv_fpbc_sn … H) -H
[ /2 width=1 by or_introl/
| * #G #L #T #H1 #H2
  /3 width=9 by fpbg_intro, or_intror/
]
qed-.

(* Basic_2A1: this was the definition of fpbg *)
lemma fpbg_inv_fpbc_fpbs (G1) (G2) (L1) (L2) (T1) (T2):
      ❨G1,L1,T1❩ > ❨G2,L2,T2❩ →
      ∃∃G,L,T. ❨G1,L1,T1❩ ≻ ❨G,L,T❩ & ❨G,L,T❩ ≥ ❨G2,L2,T2❩.
#G1 #G2 #L1 #L2 #T1 #T2 #H
elim (fpbg_inv_gen … H) -H #G3 #L3 #T3 #G4 #L4 #T4 #H13 #H34 #H42
elim (fpbs_inv_fpbc_sn … H13) -H13
[ /3 width=9 by feqg_fpbc_trans, ex2_3_intro/
| * #G #L #T #H1 #H3
  /4 width=13 by fpbg_fwd_fpbs,fpbg_intro, ex2_3_intro/
]
qed-.

(* Advanced properties of parallel rst-computation on closures **************)

lemma fpbs_fpb_trans:
      ∀F1,F2,K1,K2,T1,T2. ❨F1,K1,T1❩ ≥ ❨F2,K2,T2❩ →
      ∀G2,L2,U2. ❨F2,K2,T2❩ ≻ ❨G2,L2,U2❩ →
      ∃∃G1,L1,U1. ❨F1,K1,T1❩ ≻ ❨G1,L1,U1❩ & ❨G1,L1,U1❩ ≥ ❨G2,L2,U2❩.
#F1 #F2 #K1 #K2 #T1 #T2 #H elim (fpbs_inv_fpbg … H) -H
[ #H12 #G2 #L2 #U2 #H22
  lapply (feqg_fpbc_trans … H12 … H22) -F2 -K2 -T2
  /3 width=5 by feqg_fpbs, ex2_3_intro/
| #H12 #G2 #L2 #U2 #H22
  elim (fpbg_inv_fpbc_fpbs … H12) -H12 #F #K #T #H1 #H2
 /4 width=9 by fpbs_strap1, fpbc_fwd_fpb, ex2_3_intro/
]
qed-.
