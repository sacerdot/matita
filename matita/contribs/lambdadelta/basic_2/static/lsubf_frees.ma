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

include "basic_2/static/lsubf.ma".

(* RESTRICTED REFINEMENT FOR CONTEXT-SENSITIVE FREE VARIABLES ***************)

(* Properties with context-sensitive free variables *************************)

lemma lsubf_frees_trans: ∀f2,L2,T. L2 ⊢ 𝐅*⦃T⦄ ≘ f2 →
                         ∀f1,L1. ⦃L1, f1⦄ ⫃𝐅* ⦃L2, f2⦄ → L1 ⊢ 𝐅*⦃T⦄ ≘ f1.
#f2 #L2 #T #H elim H -f2 -L2 -T
[ /3 width=5 by lsubf_fwd_isid_dx, frees_sort/
| #f2 #i #Hf2 #g1 #Y1 #H
  elim (lsubf_inv_atom2 … H) -H #Hg1 #H destruct
  elim (eq_inv_pushs_dx … Hg1) -Hg1 #g #Hg #H destruct
  elim (eq_inv_xn … Hg) -Hg
  /3 width=3 by frees_atom, isid_eq_repl_fwd/
| #f2 #I #K2 #W #_ #IH #g1 #Y1 #H elim (lsubf_inv_pair2 … H) -H *
  [ #f1 #K1 #H12 #H1 #H2 destruct /3 width=1 by frees_pair/
  | #f #f0 #f1 #K1 #V #H12 #Hf #Hf1 #H1 #H2 #H3 destruct
    /4 width=5 by frees_pair, frees_flat/
  ]
| #f2 #I #L2 #Hf2 #g1 #Y1 #H elim (lsubf_inv_unit2 … H) -H *
  [ #f1 #L1 #H12 #H1 #H2 destruct
    /3 width=5 by lsubf_fwd_isid_dx, frees_unit/
  | #f #f0 #f1 #J #L1 #V #H12 #Hf #Hf1 #H1 #H2 destruct
    /5 width=9 by lsubf_fwd_isid_dx, frees_eq_repl_back, frees_pair, sor_isid_inv_sn/
  ]
| #f2 #I #L2 #i #_ #IH #g1 #L1 #H elim (lsubf_inv_push2 … H) -H
  /3 width=1 by frees_lref/
| /3 width=5 by lsubf_fwd_isid_dx, frees_gref/
| #f2V #f2T #f2 #p #I #L2 #V #T #_ #_ #Hf2 #IHV #IHT #f1 #L1 #H12
  elim (lsubf_inv_sor_dx … H12 … Hf2) -f2 #f1V #g1T #HV #HT #Hf1
  elim (lsubf_bind_tl_dx … (BPair I V) … HT) -HT #f1T #HT #H destruct
  /3 width=5 by frees_bind/
| #f2V #f2T #f2 #I #L2 #V #T #_ #_ #Hf2 #IHV #IHT #f1 #L1 #H12
  elim (lsubf_inv_sor_dx … H12 … Hf2) -f2 /3 width=5 by frees_flat/
]
qed-.
