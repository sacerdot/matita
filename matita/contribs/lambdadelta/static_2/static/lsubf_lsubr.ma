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

include "static_2/static/lsubr.ma".
include "static_2/static/lsubf_lsubf.ma".

(* RESTRICTED REFINEMENT FOR CONTEXT-SENSITIVE FREE VARIABLES ***************)

(* Forward lemmas with restricted refinement for local environments *********)

lemma lsubf_fwd_lsubr_isdiv:
      âf1,f2,L1,L2. âšL1,f1â© â«đ+ âšL2,f2â© â đâšf1â© â đâšf2â© â L1 â« L2.
#f1 #f2 #L1 #L2 #H elim H -f1 -f2 -L1 -L2
/4 width=3 by lsubr_bind, pr_isd_inv_next/
[ #f1 #f2 #I1 #I2 #L1 #L2 #_ #_ #H
  elim (pr_isd_inv_push âŠ H) //
| /5 width=5 by lsubf_fwd_sle, lsubr_beta, pr_sle_inv_isd_sn, pr_isd_inv_next/
| /5 width=5 by lsubf_fwd_sle, lsubr_unit, pr_sle_inv_isd_sn, pr_isd_inv_next/
]
qed-.

(* Properties with restricted refinement for local environments *************)

lemma lsubr_lsubf_isid:
      âL1,L2. L1 â« L2 â âf1,f2. đâšf1â© â đâšf2â© â âšL1,f1â© â«đ+ âšL2,f2â©.
#L1 #L2 #H elim H -L1 -L2
[ /3 width=1 by lsubf_atom, pr_isi_inv_eq_repl/
| #I #L1 #L2 | #L1 #L2 #V #W | #I1 #I2 #L1 #L2 #V
]
#_ #IH #f1 #f2 #Hf1 #Hf2
elim (pr_isi_inv_gen âŠ Hf1) -Hf1 #g1 #Hg1 #H destruct
elim (pr_isi_inv_gen âŠ Hf2) -Hf2 #g2 #Hg2 #H destruct
/3 width=1 by lsubf_push/
qed.

lemma lsubr_lsubf:
      âf2,L2,T. L2 âą đ+âšTâ© â f2 â âL1. L1 â« L2 â
      âf1. L1 âą đ+âšTâ© â f1 â âšL1,f1â© â«đ+ âšL2,f2â©.
#f2 #L2 #T #H elim H -f2 -L2 -T
[ #f2 #L2 #s #Hf2 #L1 #HL12 #f1 #Hf1
  lapply (frees_inv_sort âŠ Hf1) -Hf1 /2 width=1 by lsubr_lsubf_isid/
| #f2 #i #Hf2 #Y1 #HY1
  >(lsubr_inv_atom2 âŠ HY1) -Y1 #g1 #Hg1
  elim (frees_inv_atom âŠ Hg1) -Hg1 #f1 #Hf1 #H destruct
  /5 width=5 by lsubf_atom, pr_isi_inv_eq_repl, pr_pushs_eq_repl, pr_eq_next/
| #f2 #Z #L2 #W #_ #IH #Y1 #HY1 #g1 #Hg1 elim (lsubr_inv_pair2 âŠ HY1) -HY1 *
  [ #L1 #HL12 #H destruct
    elim (frees_inv_pair âŠ Hg1) -Hg1 #f1 #Hf1 #H destruct
    /3 width=1 by lsubf_bind/
  | #L1 #V #HL12 #H1 #H2 destruct
    elim (frees_inv_pair âŠ Hg1) -Hg1 #f1 #Hf1 #H destruct
    elim (frees_inv_flat âŠ Hf1) -Hf1 /3 width=5 by lsubf_beta/
  ]
| #f2 #I2 #L2 #Hf2 #Y1 #HY1 #g1 #Hg1 elim (lsubr_inv_unit2 âŠ HY1) -HY1 *
  [ #L1 #HL12 #H destruct
    elim (frees_inv_unit âŠ Hg1) -Hg1 #f1 #Hf1 #H destruct
    /3 width=1 by lsubf_bind, lsubr_lsubf_isid/
  | #I #L1 #V #HL12 #H destruct
    elim (frees_inv_pair âŠ Hg1) -Hg1 #f1 #Hf1 #H destruct
    /3 width=5 by lsubf_unit, pr_sor_isi_sn, lsubr_lsubf_isid/
  ]
| #f2 #I2 #L2 #i #_ #IH #Y1 #HY1 #g1 #Hg1
  elim (lsubr_fwd_bind2 âŠ HY1) -HY1 #I1 #L1 #HL12 #H destruct
  elim (frees_inv_lref âŠ Hg1) -Hg1 #f1 #Hf1 #H destruct
  /3 width=1 by lsubf_push/
|  #f2 #L2 #l #Hf2 #L1 #HL12 #f1 #Hf1
  lapply (frees_inv_gref âŠ Hf1) -Hf1 /2 width=1 by lsubr_lsubf_isid/
| #f2V #f2T #f2 #p #I #L2 #V #T #_ #_ #Hf2 #IHV #IHT #L1 #HL12 #f1 #Hf1
  elim (frees_inv_bind âŠ Hf1) -Hf1 #f1V #f1T #Hf1V #Hf1T #Hf1
  /5 width=8 by lsubf_sor, lsubf_fwd_bind_tl, lsubr_bind/
| #f2V #f2T #f2 #I #L2 #V #T #_ #_ #Hf2 #IHV #IHT #L1 #HL12 #f1 #Hf1
  elim (frees_inv_flat âŠ Hf1) -Hf1 #f1V #f1T #Hf1V #Hf1T #Hf1
  /3 width=8 by lsubf_sor/
]
qed.
