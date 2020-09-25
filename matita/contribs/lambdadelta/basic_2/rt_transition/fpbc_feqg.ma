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

include "basic_2/rt_transition/fpb_feqg.ma".
include "basic_2/rt_transition/fpbc.ma".

(* PROPER PARALLEL RST-TRANSITION FOR CLOSURES ******************************)

(* Properties with generic equivalence for closures *************************)

(* Basic_2A1: uses: teqg_fpb_trans lleq_fpb_trans fleq_fpb_trans *)
lemma feqg_fpbc_trans (S) (G) (L) (T):
      reflexive … S → symmetric … S → Transitive … S →
      ∀G1,L1,T1. ❪G1,L1,T1❫ ≛[S] ❪G,L,T❫ →
      ∀G2,L2,T2. ❪G,L,T❫ ≻ ❪G2,L2,T2❫ → ❪G1,L1,T1❫ ≻ ❪G2,L2,T2❫.
#S #G #L #T #H1S #H2S #H3S #G1 #L1 #T1 #H1 #G2 #L2 #T2 #H2
elim (fpbc_inv_gen sfull … H2) -H2 #H2 #Hn2
/6 width=9 by fpbc_intro, feqg_fpb_trans, feqg_canc_sn, feqg_feqx/
qed-.

(* Inversion lemmas with generic equivalence for closures *******************)

(* Basic_2A1: uses: fpb_inv_fleq *)
lemma fpbc_inv_feqg (S):
      ∀G1,G2,L1,L2,T1,T2. ❪G1,L1,T1❫ ≻ ❪G2,L2,T2❫ →
      ❪G1,L1,T1❫ ≛[S] ❪G2,L2,T2❫ → ⊥.
#S #G1 #G2 #L1 #L2 #T1 #T2 #H #H12
elim (fpbc_inv_gen S … H) -H #_ #Hn2
/2 width=1 by/
qed-.
