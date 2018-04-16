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

include "basic_2/static/lsubr.ma".
include "basic_2/static/lsubf_lsubf.ma".

(* RESTRICTED REFINEMENT FOR CONTEXT-SENSITIVE FREE VARIABLES ***************)

(* Forward lemmas with restricted refinement for local environments *********)

lemma lsubf_fwd_lsubr_isdiv: ∀f1,f2,L1,L2. ⦃L1, f1⦄ ⫃𝐅* ⦃L2, f2⦄ →
                             𝛀⦃f1⦄ → 𝛀⦃f2⦄ → L1 ⫃ L2.
#f1 #f2 #L1 #L2 #H elim H -f1 -f2 -L1 -L2
/4 width=3 by lsubr_bind, isdiv_inv_next/
[ #f1 #f2 #I1 #I2 #L1 #L2 #_ #_ #H
  elim (isdiv_inv_push … H) //
| /5 width=5 by lsubf_fwd_sle, lsubr_beta, sle_inv_isdiv_sn, isdiv_inv_next/
| /5 width=5 by lsubf_fwd_sle, lsubr_unit, sle_inv_isdiv_sn, isdiv_inv_next/
]
qed-.

(* Properties with restricted refinement for local environments *************)

lemma lsubr_lsubf_isid: ∀L1,L2. L1 ⫃ L2 →
                        ∀f1,f2. 𝐈⦃f1⦄ → 𝐈⦃f2⦄ → ⦃L1, f1⦄ ⫃𝐅* ⦃L2, f2⦄.
#L1 #L2 #H elim H -L1 -L2
[ /3 width=1 by lsubf_atom, isid_inv_eq_repl/
| #I #L1 #L2 | #L1 #L2 #V #W | #I1 #I2 #L1 #L2 #V
]
#_ #IH #f1 #f2 #Hf1 #Hf2
elim (isid_inv_gen … Hf1) -Hf1 #g1 #Hg1 #H destruct
elim (isid_inv_gen … Hf2) -Hf2 #g2 #Hg2 #H destruct
/3 width=1 by lsubf_push/
qed.

lemma lsubr_lsubf: ∀f2,L2,T. L2 ⊢ 𝐅*⦃T⦄ ≘ f2 → ∀L1. L1 ⫃ L2 →
                   ∀f1. L1 ⊢ 𝐅*⦃T⦄ ≘ f1 → ⦃L1, f1⦄ ⫃𝐅* ⦃L2, f2⦄.
#f2 #L2 #T #H elim H -f2 -L2 -T
[ #f2 #L2 #s #Hf2 #L1 #HL12 #f1 #Hf1
  lapply (frees_inv_sort … Hf1) -Hf1 /2 width=1 by lsubr_lsubf_isid/
| #f2 #i #Hf2 #Y1 #HY1
  >(lsubr_inv_atom2 … HY1) -Y1 #g1 #Hg1
  elim (frees_inv_atom … Hg1) -Hg1 #f1 #Hf1 #H destruct
  /5 width=5 by lsubf_atom, isid_inv_eq_repl, pushs_eq_repl, eq_next/
| #f2 #Z #L2 #W #_ #IH #Y1 #HY1 #g1 #Hg1 elim (lsubr_inv_pair2 … HY1) -HY1 *
  [ #L1 #HL12 #H destruct
    elim (frees_inv_pair … Hg1) -Hg1 #f1 #Hf1 #H destruct
    /3 width=1 by lsubf_bind/
  | #L1 #V #HL12 #H1 #H2 destruct
    elim (frees_inv_pair … Hg1) -Hg1 #f1 #Hf1 #H destruct
    elim (frees_inv_flat … Hf1) -Hf1 /3 width=5 by lsubf_beta/
  ]
| #f2 #I2 #L2 #Hf2 #Y1 #HY1 #g1 #Hg1 elim (lsubr_inv_unit2 … HY1) -HY1 *
  [ #L1 #HL12 #H destruct
    elim (frees_inv_unit … Hg1) -Hg1 #f1 #Hf1 #H destruct
    /3 width=1 by lsubf_bind, lsubr_lsubf_isid/
  | #I #L1 #V #HL12 #H destruct
    elim (frees_inv_pair … Hg1) -Hg1 #f1 #Hf1 #H destruct
    /3 width=5 by lsubf_unit, sor_isid_sn, lsubr_lsubf_isid/
  ]
| #f2 #I2 #L2 #i #_ #IH #Y1 #HY1 #g1 #Hg1
  elim (lsubr_fwd_bind2 … HY1) -HY1 #I1 #L1 #HL12 #H destruct
  elim (frees_inv_lref … Hg1) -Hg1 #f1 #Hf1 #H destruct
  /3 width=1 by lsubf_push/
|  #f2 #L2 #l #Hf2 #L1 #HL12 #f1 #Hf1
  lapply (frees_inv_gref … Hf1) -Hf1 /2 width=1 by lsubr_lsubf_isid/
| #f2V #f2T #f2 #p #I #L2 #V #T #_ #_ #Hf2 #IHV #IHT #L1 #HL12 #f1 #Hf1
  elim (frees_inv_bind … Hf1) -Hf1 #f1V #f1T #Hf1V #Hf1T #Hf1
  /5 width=8 by lsubf_sor, lsubf_fwd_bind_tl, lsubr_bind/
| #f2V #f2T #f2 #I #L2 #V #T #_ #_ #Hf2 #IHV #IHT #L1 #HL12 #f1 #Hf1
  elim (frees_inv_flat … Hf1) -Hf1 #f1V #f1T #Hf1V #Hf1T #Hf1
  /3 width=8 by lsubf_sor/
]
qed.
