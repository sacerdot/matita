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

include "basic_2/static/aaa_fqus.ma".
include "basic_2/static/aaa_lleq.ma".
include "basic_2/reduction/lpx_aaa.ma".
include "basic_2/reduction/fpb.ma".

(* "BIG TREE" PARALLEL REDUCTION FOR CLOSURES *******************************)

(* Properties on atomic arity assignment for terms **************************)

lemma fpb_aaa_conf: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≽[h, g] ⦃G2, L2, T2⦄ →
                    ∀A1. ⦃G1, L1⦄ ⊢ T1 ⁝ A1 → ∃A2. ⦃G2, L2⦄ ⊢ T2 ⁝ A2.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 * -G2 -L2 -T2
/3 width=6 by aaa_lleq_conf, lpx_aaa_conf, cpx_aaa_conf, aaa_fquq_conf, ex_intro/
qed-.
