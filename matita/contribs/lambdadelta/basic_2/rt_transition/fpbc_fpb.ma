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

include "static_2/static/feqx_feqx.ma".
include "basic_2/rt_transition/fpbc.ma".

(* PROPER PARALLEL RST-TRANSITION FOR CLOSURES ******************************)

(* Inversrion lemmas with parallel rst-transition for closures **************)

(* Basic_2A1: uses: fpbq_ind_alt *)
lemma fpb_inv_fpbc:
      ∀G1,G2,L1,L2,T1,T2. ❪G1,L1,T1❫ ≽ ❪G2,L2,T2❫ →
      ∨∨ ❪G1,L1,T1❫ ≅ ❪G2,L2,T2❫
       | ❪G1,L1,T1❫ ≻ ❪G2,L2,T2❫.
#G1 #G2 #L1 #L2 #T1 #T2 #H 
elim (feqx_dec G1 G2 L1 L2 T1 T2)
/4 width=1 by fpbc_intro, or_intror, or_introl/
qed-.
