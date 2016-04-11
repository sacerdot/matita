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

include "basic_2/notation/relations/lazyeq_6.ma".
include "basic_2/grammar/genv.ma".
include "basic_2/static/frees_fqup.ma".
include "basic_2/static/frees_lreq.ma".

(* RANGED EQUIVALENCE FOR CLOSURES ******************************************)

inductive freq (G) (L1) (T): relation3 genv lenv term ≝
| fleq_intro: ∀L2,f. L1 ⊢ 𝐅*⦃T⦄ ≡ f → L1 ≡[f] L2 → freq G L1 T G L2 T
.

interpretation
   "ranged equivalence (closure)"
   'LazyEq G1 L1 T1 G2 L2 T2 = (freq G1 L1 T1 G2 L2 T2).

(* Basic properties *********************************************************)

lemma freq_refl: tri_reflexive … freq.
#G #L #T elim (frees_total L T) /2 width=3 by fleq_intro/
qed.

lemma freq_sym: tri_symmetric … freq.
#G1 #L1 #T1 #G2 #L2 #T2 * /4 width=3 by fleq_intro, frees_lreq_conf, lreq_sym/
qed-.

(* Basic inversion lemmas ***************************************************)

lemma freq_inv_gen: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≡ ⦃G2, L2, T2⦄ →
                    ∃∃f. G1 = G2 & L1 ⊢ 𝐅*⦃T1⦄ ≡ f & L1 ≡[f] L2 & T1 = T2.
#G1 #G2 #L1 #L2 #T1 #T2 * -G2 -L2 -T2 /2 width=3 by ex4_intro/
qed-.

(* Basic_2A1: removed theorems 6:
              fleq_refl fleq_sym fleq_inv_gen
              fleq_trans fleq_canc_sn fleq_canc_dx
*)
