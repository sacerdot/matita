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

include "basic_2/static/rdeq_req.ma".
include "basic_2/static/fdeq.ma".

(* DEGREE-BASED EQUIVALENCE FOR CLOSURES ON REFERRED ENTRIES ****************)

(* Properties with syntactic equivalence on referred entries ****************)

lemma req_rdeq_trans: ∀h,o,L1,L,T1. L1 ≡[T1] L →
                      ∀G1,G2,L2,T2. ⦃G1, L, T1⦄ ≛[h, o] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ≛[h, o] ⦃G2, L2, T2⦄.
#h #o #L1 #L #T1 #HL1 #G1 #G2 #L2 #T2 #H
elim (fdeq_inv_gen_sn … H) -H #H #HL2 #T12 destruct
/3 width=3 by fdeq_intro_sn, req_rdeq_trans/
qed-.
