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

lemma lsubf_frees_trans: ∀f2,L2,T. L2 ⊢ 𝐅*⦃T⦄ ≡ f2 → ∀f,L1. ⦃L1, f⦄ ⫃𝐅* ⦃L2, f2⦄ →
                         ∃∃f1. L1 ⊢ 𝐅*⦃T⦄ ≡ f1 & f1 ⊆ f.
#f2 #L2 #T #H elim H -f2 -L2 -T
[ #f2 #I #Hf2 #f #L1 #H elim (lsubf_inv_atom2 … H) -H
  #H #_ destruct /3 width=3 by frees_atom, sle_isid_sn, ex2_intro/
| #f2 #I #K2 #W #s #_ #IH #f #L1 #H elim (lsubf_inv_pair2 … H) -H *
  [ #K1 #_ #H12 #H | #g #K1 #V #Hg #Hf #_ #H12 #H1 #H2 ]
  destruct elim (IH … H12) -K2
  /3 width=3 by frees_sort, sle_inv_tl_dx, ex2_intro/
| #f2 #I #K2 #W #_ #IH #f #L1 #H elim (lsubf_inv_pair2 … H) -H *
  [ #K1 #H elim (sle_inv_nx … H ??) -H [ <tl_next_rew |*: // ]
    #g2 #_ #H1 #H12 #H2 destruct elim (IH … H12) -K2
    /3 width=7 by frees_zero, sle_next, ex2_intro/
  | #g #K1 #V #Hg #Hf #H elim (sle_inv_nx … H ??) -H [ <tl_next_rew |*: // ]
    #g2 #_ #H1 #H12 #H2 #H3 destruct elim (IH … H12) -K2
    #f1 #Hf1 elim (sor_isfin_ex … f1 g ??)
    /4 width=7 by frees_fwd_isfin, frees_flat, frees_zero, sor_inv_sle, sle_next, ex2_intro/
  ]
| #f2 #I #K2 #W #i #_ #IH #f #L1 #H elim (lsubf_inv_pair2 … H) -H *
  [ #K1 #_ #H12 #H | #g #K1 #V #Hg #Hf #_ #H12 #H1 #H2 ]
  destruct elim (IH … H12) -K2
  /3 width=3 by frees_lref, sle_inv_tl_dx, ex2_intro/
| #f2 #I #K2 #W #l #_ #IH #f #L1 #H elim (lsubf_inv_pair2 … H) -H *
  [ #K1 #_ #H12 #H | #g #K1 #V #Hg #Hf #_ #H12 #H1 #H2 ]
  destruct elim (IH … H12) -K2
  /3 width=3 by frees_gref, sle_inv_tl_dx, ex2_intro/
| #f2V #f2T #f2 #p #I #L2 #V #T #_ #_ #Hf2 #IHV #IHT #f #L1 #H12
  elim (IHV f L1) -IHV [2: /3 width=4 by lsubf_sle_div, sor_inv_sle_sn/ ]
  elim (IHT (⫯f) (L1.ⓑ{I}V)) -IHT [2: /4 width=4 by lsubf_sle_div, lsubf_pair_nn, sor_inv_sle_dx, sor_inv_tl_dx/ ]
  -f2V -f2T -f2 -L2 #f1T #HT #Hf1T #f1V #HV #Hf1V elim (sor_isfin_ex … f1V (⫱f1T) ??)
  /4 width=9 by frees_fwd_isfin, frees_bind, sor_inv_sle, sle_xn_tl, isfin_tl, ex2_intro/
| #f2V #f2T #f2 #I #L2 #V #T #_ #_ #Hf2 #IHV #IHT #f #L1 #H12
  elim (IHV f L1) -IHV [2: /3 width=4 by lsubf_sle_div, sor_inv_sle_sn/ ]
  elim (IHT f L1) -IHT [2: /3 width=4 by lsubf_sle_div, sor_inv_sle_dx/ ]
  -f2V -f2T -f2 -L2 #f1T #HT #Hf1T #f1V #HV #Hf1V elim (sor_isfin_ex … f1V f1T ??)
  /3 width=7 by frees_fwd_isfin, frees_flat, sor_inv_sle, ex2_intro/
]
qed-.
