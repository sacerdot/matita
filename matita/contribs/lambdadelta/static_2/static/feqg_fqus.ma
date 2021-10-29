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

include "static_2/static/reqg_fqus.ma".
include "static_2/static/feqg.ma".

(* GENERIC EQUIVALENCE FOR CLOSURES ON REFERRED ENTRIES *********************)

(* Properties with star-iterated structural successor for closures **********)

lemma feqg_fquq_trans (S) (b):
      reflexive … S → symmetric … S → Transitive … S →
      ∀G1,G,L1,L,T1,T. ❨G1,L1,T1❩ ≛[S] ❨G,L,T❩ →
      ∀G2,L2,T2. ❨G,L,T❩ ⬂⸮[b] ❨G2,L2,T2❩ →
      ∃∃G,L0,T0. ❨G1,L1,T1❩ ⬂⸮[b] ❨G,L0,T0❩ & ❨G,L0,T0❩ ≛[S] ❨G2,L2,T2❩.
#S #b #H1S #H2S #H3S #G1 #G #L1 #L #T1 #T #H1 #G2 #L2 #T2 #H2
elim(feqg_inv_gen_dx … H1) -H1 // #HG #HL1 #HT1 destruct
elim (reqg_fquq_trans … H2 … HL1) -L // #L #T0 #H2 #HT02 #HL2
elim (teqg_fquq_trans … H2 … HT1) -T // #L0 #T #H2 #HT0 #HL0
lapply (teqg_reqg_conf_sn … HT02 … HL0) -HL0 // #HL0
/4 width=7 by feqg_intro_dx, reqg_trans, teqg_trans, ex2_3_intro/
qed-.

lemma feqg_fqus_trans (S) (b):
      reflexive … S → symmetric … S → Transitive … S →
      ∀G1,G,L1,L,T1,T. ❨G1,L1,T1❩ ≛[S] ❨G,L,T❩ →
      ∀G2,L2,T2. ❨G,L,T❩ ⬂*[b] ❨G2,L2,T2❩ →
      ∃∃G,L0,T0. ❨G1,L1,T1❩ ⬂*[b] ❨G,L0,T0❩ & ❨G,L0,T0❩ ≛[S] ❨G2,L2,T2❩.
#S #b #H1S #H2S #H3S #G1 #G #L1 #L #T1 #T #H1 #G2 #L2 #T2 #H2
elim(feqg_inv_gen_dx … H1) -H1 // #HG #HL1 #HT1 destruct
elim (reqg_fqus_trans … H2 … HL1) -L // #L #T0 #H2 #HT02 #HL2
elim (teqg_fqus_trans … H2 … HT1) -T // #L0 #T #H2 #HT0 #HL0
lapply (teqg_reqg_conf_sn … HT02 … HL0) -HL0 // #HL0
/4 width=7 by feqg_intro_dx, reqg_trans, teqg_trans, ex2_3_intro/
qed-.
