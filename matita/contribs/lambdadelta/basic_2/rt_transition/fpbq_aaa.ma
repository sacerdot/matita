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

include "static_2/static/aaa_fqus.ma".
include "static_2/static/aaa_feqx.ma".
include "basic_2/rt_transition/lpx_aaa.ma".
include "basic_2/rt_transition/fpbq.ma".

(* PARALLEL RST-TRANSITION FOR CLOSURES *************************************)

(* Properties with atomic arity assignment for terms ************************)

lemma fpbq_aaa_conf:
      ∀G1,G2,L1,L2,T1,T2. ❪G1,L1,T1❫ ≽ ❪G2,L2,T2❫ →
      ∀A1. ❪G1,L1❫ ⊢ T1 ⁝ A1 → ∃A2. ❪G2,L2❫ ⊢ T2 ⁝ A2.
#G1 #G2 #L1 #L2 #T1 #T2 * -G2 -L2 -T2
/3 width=8 by lpx_aaa_conf, cpx_aaa_conf, aaa_feqx_conf, aaa_fquq_conf, ex_intro/
qed-.
