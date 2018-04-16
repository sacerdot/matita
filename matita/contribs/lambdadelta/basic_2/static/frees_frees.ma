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

include "basic_2/static/frees.ma".

(* CONTEXT-SENSITIVE FREE VARIABLES *****************************************)

(* Main inversion lemmas ****************************************************)

theorem frees_mono: ∀f1,L,T. L ⊢ 𝐅*⦃T⦄ ≘ f1 → ∀f2. L ⊢ 𝐅*⦃T⦄ ≘ f2 → f1 ≗ f2.
#f1 #L #T #H elim H -f1 -L -T
[ /3 width=3 by frees_inv_sort, isid_inv_eq_repl/
| #f1 #i #Hf1 #g2 #H
  elim (frees_inv_atom … H) -H #f2 #Hf2 #H destruct
  /4 width=5 by isid_inv_eq_repl, pushs_eq_repl, eq_next/
| #f1 #I #L #V #_ #IH #g2 #H elim (frees_inv_pair … H) -H
  #f2 #Hf2 #H destruct /3 width=5 by eq_next/
| #f1 #I #L #Hf1 #g2 #H elim (frees_inv_unit … H) -H
  #f2 #Hf2 #H destruct /3 width=5 by isid_inv_eq_repl, eq_next/
| #f1 #I #L #i #_ #IH #g2 #H elim (frees_inv_lref … H) -H
  #f2 #Hf2 #H destruct /3 width=5 by eq_push/
| /3 width=3 by frees_inv_gref, isid_inv_eq_repl/
| #f1V #f1T #f1 #p #I #L #V #T #_ #_ #Hf1 #IHV #IHT #f2 #H elim (frees_inv_bind … H) -H
  #f2V #f2T #HV #HT #Hf2 @(sor_mono … Hf1) -Hf1
  /5 width=3 by sor_eq_repl_fwd2, sor_eq_repl_fwd1, tl_eq_repl/ (**) (* full auto too slow *)
| #f1V #f1T #f1 #I #L #V #T #_ #_ #Hf1 #IHV #IHT #f2 #H elim (frees_inv_flat … H) -H
  #f2V #f2T #HV #HT #Hf2 @(sor_mono … Hf1) -Hf1
  /4 width=3 by sor_eq_repl_fwd2, sor_eq_repl_fwd1/ (**) (* full auto too slow *)
]
qed-.
