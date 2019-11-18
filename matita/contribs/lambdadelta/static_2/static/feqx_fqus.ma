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

include "static_2/static/reqx_fqus.ma".
include "static_2/static/feqx.ma".

(* SORT-IRRELEVANT EQUIVALENCE FOR CLOSURES ON REFERRED ENTRIES *************)

(* Properties with star-iterated structural successor for closures **********)

lemma feqx_fqus_trans: ∀b,G1,G,L1,L,T1,T. ⦃G1,L1,T1⦄ ≛ ⦃G,L,T⦄ →
                       ∀G2,L2,T2. ⦃G,L,T⦄ ⬂*[b] ⦃G2,L2,T2⦄ →
                       ∃∃G,L0,T0. ⦃G1,L1,T1⦄ ⬂*[b] ⦃G,L0,T0⦄ & ⦃G,L0,T0⦄ ≛ ⦃G2,L2,T2⦄.
#b #G1 #G #L1 #L #T1 #T #H1 #G2 #L2 #T2 #H2
elim(feqx_inv_gen_dx … H1) -H1 #HG #HL1 #HT1 destruct
elim (reqx_fqus_trans … H2 … HL1) -L #L #T0 #H2 #HT02 #HL2
elim (teqx_fqus_trans … H2 … HT1) -T #L0 #T #H2 #HT0 #HL0
lapply (teqx_reqx_conf … HT02 … HL0) -HL0 #HL0
/4 width=7 by feqx_intro_dx, reqx_trans, teqx_trans, ex2_3_intro/
qed-.
