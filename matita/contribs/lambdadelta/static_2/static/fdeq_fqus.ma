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

include "static_2/static/rdeq_fqus.ma".
include "static_2/static/fdeq.ma".

(* DEGREE-BASED EQUIVALENCE FOR CLOSURES ON REFERRED ENTRIES ****************)

(* Properties with star-iterated structural successor for closures **********)

lemma fdeq_fqus_trans: ∀h,o,b,G1,G,L1,L,T1,T. ⦃G1, L1, T1⦄ ≛[h, o] ⦃G, L, T⦄ →
                       ∀G2,L2,T2. ⦃G, L, T⦄ ⊐*[b] ⦃G2, L2, T2⦄ →
                       ∃∃G,L0,T0. ⦃G1, L1, T1⦄ ⊐*[b] ⦃G, L0, T0⦄ & ⦃G, L0, T0⦄ ≛[h, o] ⦃G2, L2, T2⦄.
#h #o #b #G1 #G #L1 #L #T1 #T #H1 #G2 #L2 #T2 #H2
elim(fdeq_inv_gen_dx … H1) -H1 #HG #HL1 #HT1 destruct
elim (rdeq_fqus_trans … H2 … HL1) -L #L #T0 #H2 #HT02 #HL2
elim (tdeq_fqus_trans … H2 … HT1) -T #L0 #T #H2 #HT0 #HL0
lapply (tdeq_rdeq_conf … HT02 … HL0) -HL0 #HL0
/4 width=7 by fdeq_intro_dx, rdeq_trans, tdeq_trans, ex2_3_intro/
qed-.