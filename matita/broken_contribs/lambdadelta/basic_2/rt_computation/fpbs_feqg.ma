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

include "static_2/static/feqg_fqup.ma".
include "basic_2/rt_transition/fpb_feqg.ma".
include "basic_2/rt_computation/fpbs_fqup.ma".

(* PARALLEL RST-COMPUTATION FOR CLOSURES ************************************)

(* Propreties with generic equivalence on referred closures *****************)

(* Basic_2A1: uses: lleq_fpbs fleq_fpbs *)
lemma feqg_fpbs (S) (G1) (G2) (L1) (L2) (T1) (T2):
      reflexive … S → symmetric … S →
      ❨G1,L1,T1❩ ≛[S] ❨G2,L2,T2❩ → ❨G1,L1,T1❩ ≥ ❨G2,L2,T2❩.
/3 width=5 by fpb_fpbs, feqg_fpb/ qed.

(* Basic_2A1: uses: fpbs_lleq_trans *)
lemma fpbs_feqg_trans (S) (G) (L) (T):
      reflexive … S → symmetric … S →
      ∀G1,L1,T1. ❨G1,L1,T1❩ ≥ ❨G,L,T❩ →
      ∀G2,L2,T2. ❨G,L,T❩ ≛[S] ❨G2,L2,T2❩ → ❨G1,L1,T1❩ ≥ ❨G2,L2,T2❩.
/3 width=9 by fpbs_strap1, feqg_fpb/ qed-.

(* Basic_2A1: uses: lleq_fpbs_trans *)
lemma feqg_fpbs_trans (S) (G) (L) (T):
      reflexive … S → symmetric … S →
      ∀G2,L2,T2. ❨G,L,T❩ ≥ ❨G2,L2,T2❩ →
      ∀G1,L1,T1. ❨G1,L1,T1❩ ≛[S] ❨G,L,T❩ → ❨G1,L1,T1❩ ≥ ❨G2,L2,T2❩.
/3 width=5 by fpbs_strap2, feqg_fpb/ qed-.

lemma teqg_fpbs_trans (S) (T):
      reflexive … S → symmetric … S →
      ∀T1. T1 ≛[S] T →
      ∀G1,G2,L1,L2,T2. ❨G1,L1,T❩ ≥ ❨G2,L2,T2❩ → ❨G1,L1,T1❩ ≥ ❨G2,L2,T2❩.
/3 width=8 by feqg_fpbs_trans, teqg_feqg/ qed-.

lemma fpbs_teqg_trans (S) (T):
      reflexive … S → symmetric … S →
      ∀G1,G2,L1,L2,T1. ❨G1,L1,T1❩ ≥ ❨G2,L2,T❩ →
      ∀T2. T ≛[S] T2 → ❨G1,L1,T1❩ ≥ ❨G2,L2,T2❩.
/3 width=8 by fpbs_feqg_trans, teqg_feqg/ qed-.
