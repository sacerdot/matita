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

include "static_2/static/reqx_req.ma".
include "static_2/static/feqx.ma".

(* SORT-IRRELEVANT EQUIVALENCE FOR CLOSURES ON REFERRED ENTRIES *************)

(* Properties with syntactic equivalence on referred entries ****************)

lemma req_reqx_trans: ∀L1,L,T1. L1 ≡[T1] L →
                      ∀G1,G2,L2,T2. ⦃G1,L,T1⦄ ≛ ⦃G2,L2,T2⦄ → ⦃G1,L1,T1⦄ ≛ ⦃G2,L2,T2⦄.
#L1 #L #T1 #HL1 #G1 #G2 #L2 #T2 #H
elim (feqx_inv_gen_sn … H) -H #H #HL2 #T12 destruct
/3 width=3 by feqx_intro_sn, req_reqx_trans/
qed-.
