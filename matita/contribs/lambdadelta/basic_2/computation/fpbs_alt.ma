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

include "basic_2/notation/relations/btpredstaralt_8.ma".
include "basic_2/computation/lpxs_cpxs.ma".
include "basic_2/computation/fpbs_fpbs.ma".

(* "BIG TREE" PARALLEL COMPUTATION FOR CLOSURES *****************************)

(* Note: alternative definition of fpbs *)
definition fpbsa: ∀h. sd h → tri_relation genv lenv term ≝
                  λh,g,G1,L1,T1,G2,L2,T2.
                  ∃∃L,T. ⦃G1, L1⦄ ⊢ T1 ➡*[h, g] T &
                         ⦃G1, L1, T⦄ ⊃* ⦃G2, L, T2⦄ &
                         ⦃G2, L⦄ ⊢ ➡*[h, g] L2.

interpretation "'big tree' parallel computation (closure) alternative"
   'BTPRedStarAlt h g G1 L1 T1 G2 L2 T2 = (fpbsa h g G1 L1 T1 G2 L2 T2).

(* Basic properties *********************************************************)

lemma fpb_fpbsa_trans: ∀h,g,G1,G,L1,L,T1,T. ⦃G1, L1, T1⦄ ≽[h, g] ⦃G, L, T⦄ →
                       ∀G2,L2,T2. ⦃G, L, T⦄ ≥≥[h, g] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ≥≥[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G #L1 #L #T1 #T * -G -L -T [ #G #L #T #HG1 | #T #HT1 | #L #HL1 ]
#G2 #L2 #T2 * #L0 #T0 #HT0 #HG2 #HL02
[ elim (fquq_cpxs_trans … HT0 … HG1) -T
  /3 width=7 by fqus_strap2, ex3_2_intro/
| /3 width=5 by cpxs_strap2, ex3_2_intro/
| lapply (lpx_cpxs_trans … HT0 … HL1) -HT0
  elim (lpx_fqus_trans … HG2 … HL1) -L
  /3 width=7 by lpxs_strap2, cpxs_trans, ex3_2_intro/
] 
qed-.

(* Main properties **********************************************************)

theorem fpbs_fpbsa: ∀h,g,G1,G2,L1,L2,T1,T2.
                    ⦃G1, L1, T1⦄ ≥[h, g] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ≥≥[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H @(fpbs_ind_dx … H) -G1 -L1 -T1
/2 width=5 by fpb_fpbsa_trans, ex3_2_intro/
qed.

(* Main inversion lemmas ****************************************************)

theorem fpbsa_inv_fpbs: ∀h,g,G1,G2,L1,L2,T1,T2.
                        ⦃G1, L1, T1⦄ ≥≥[h, g] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ≥[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 *
/4 width=5 by fpbs_trans, fqus_fpbs, cpxs_fpbs, lpxs_fpbs/
qed-.
