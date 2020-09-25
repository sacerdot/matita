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

include "basic_2/rt_computation/fpbs_fqup.ma".
include "basic_2/rt_computation/fpbg.ma".

(* PROPER PARALLEL RST-COMPUTATION FOR CLOSURES *****************************)

(* Advanced properties ******************************************************)

lemma fpbc_fpbg (G1) (G2) (L1) (L2) (T1) (T2):
      ❪G1,L1,T1❫ ≻ ❪G2,L2,T2❫ → ❪G1,L1,T1❫ > ❪G2,L2,T2❫.
/3 width=13 by fpbg_intro, fpb_fpbs/ qed.

lemma fpbc_fpbs_fpbg (G) (L) (T):
      ∀G1,L1,T1. ❪G1,L1,T1❫ ≻ ❪G,L,T❫ →
      ∀G2,L2,T2. ❪G,L,T❫ ≥ ❪G2,L2,T2❫ → ❪G1,L1,T1❫ > ❪G2,L2,T2❫.
/2 width=9 by fpbg_intro/ qed.
