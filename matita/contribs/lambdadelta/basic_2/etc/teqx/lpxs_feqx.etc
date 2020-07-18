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

include "static_2/static/feqx.ma".
include "basic_2/rt_computation/lpxs_reqx.ma".

(* EXTENDED PARALLEL RT-COMPUTATION FOR FULL LOCAL ENVIRONMENTS **************)

(* Properties with sort-irrelevant equivalence on closures ******************)

lemma feqx_lpxs_trans:
      ∀G1,G2,L1,L0,T1,T2. ❪G1,L1,T1❫ ≛ ❪G2,L0,T2❫ →
      ∀L2. ❪G2,L0❫ ⊢⬈* L2 →
      ∃∃L. ❪G1,L1❫ ⊢⬈* L & ❪G1,L,T1❫ ≛ ❪G2,L2,T2❫.
#G1 #G2 #L1 #L0 #T1 #T2 #H1 #L2 #HL02
elim (feqx_inv_gen_dx … H1) -H1 #HG #HL10 #HT12 destruct
elim (reqx_lpxs_trans … HL02 … HL10) -L0 #L0 #HL10 #HL02
/3 width=3 by feqx_intro_dx, ex2_intro/
qed-.
