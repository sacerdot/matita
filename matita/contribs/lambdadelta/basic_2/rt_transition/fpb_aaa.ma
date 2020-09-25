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
include "static_2/static/aaa_reqg.ma".
include "basic_2/rt_transition/lpx_aaa.ma".
include "basic_2/rt_transition/fpb_lpx.ma".

(* PARALLEL RST-TRANSITION FOR CLOSURES *************************************)

(* Properties with atomic arity assignment for terms ************************)

(* Basic_2A1: uses: fpbq_aaa_conf *)
lemma fpb_aaa_conf:
      ∀G1,G2,L1,L2,T1,T2. ❪G1,L1,T1❫ ≽ ❪G2,L2,T2❫ →
      ∀A1. ❪G1,L1❫ ⊢ T1 ⁝ A1 → ∃A2. ❪G2,L2❫ ⊢ T2 ⁝ A2.
#G1 #G2 #L1 #L2 #T1 #T2 #H #A1 #HA1
elim (fpb_inv_req … H) -H #L0 #L #T #H1 #HT2 #HL0 #HL02
elim (aaa_fquq_conf … H1 … HA1) -G1 -L1 -T1 -A1 #A2 #HA2
lapply (cpx_reqg_conf … HL0 … HT2) -HT2 // #HT2
/4 width=6 by cpx_aaa_conf_lpx, aaa_reqg_conf, ex_intro/
qed-.
