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

theorem frees_mono: ∀L,T,f1. L ⊢ 𝐅*⦃T⦄ ≡ f1 → ∀f2. L ⊢ 𝐅*⦃T⦄ ≡ f2 → f1 ≗ f2.
#L #T #f1 #H elim H -L -T -f1
[ /3 width=2 by frees_inv_atom, isid_inv_eq_repl/
| /4 width=5 by frees_inv_sort, eq_push_inv_isid, isid_inv_eq_repl, eq_trans/
| #I #L #V #f1 #_ #IH #x #H elim (frees_inv_zero … H) -H *
  [ #H destruct
  | #Z #Y #X #f2 #Hf2 #H1 #H2 destruct /3 width=5 by eq_next/
  ]
| #I #L #V #i #f1 #_ #IH #x #H elim (frees_inv_lref … H) -H *
  [ #H destruct
  | #Z #Y #X #f2 #Hf2 #H1 #H2 destruct /3 width=5 by eq_push/
  ]
| /4 width=5 by frees_inv_gref, eq_push_inv_isid, isid_inv_eq_repl, eq_trans/
| #I #L #V #T #p #f1 #f2 #f #_ #_ #Hf #IHV #IHT #g #H elim (frees_inv_bind … H) -H
  #g1 #g2 #HV #HT #Hg @(sor_mono … Hf) -Hf
  /5 width=3 by sor_eq_repl_fwd2, sor_eq_repl_fwd1, tl_eq_repl/ (**) (* full auto too slow *)
| #I #L #V #T #f1 #f2 #f #_ #_ #Hf #IHV #IHT #g #H elim (frees_inv_flat … H) -H
  #g1 #g2 #HV #HT #Hg @(sor_mono … Hf) -Hf
  /4 width=3 by sor_eq_repl_fwd2, sor_eq_repl_fwd1/ (**) (* full auto too slow *)
]
qed-.
