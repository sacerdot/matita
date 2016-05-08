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

theorem frees_mono: ∀f1,L,T. L ⊢ 𝐅*⦃T⦄ ≡ f1 → ∀f2. L ⊢ 𝐅*⦃T⦄ ≡ f2 → f1 ≗ f2.
#f1 #L #T #H elim H -f1 -L -T
[ /3 width=2 by frees_inv_atom, isid_inv_eq_repl/
| /4 width=5 by frees_inv_sort, eq_push_inv_isid, isid_inv_eq_repl, eq_trans/
| #f1 #I #L #V #_ #IH #x #H elim (frees_inv_zero … H) -H *
  [ #H destruct
  | #f2 #Z #Y #X #Hf2 #H1 #H2 destruct /3 width=5 by eq_next/
  ]
| #f1 #I #L #V #i #_ #IH #x #H elim (frees_inv_lref … H) -H *
  [ #H destruct
  | #f2 #Z #Y #X #Hf2 #H1 #H2 destruct /3 width=5 by eq_push/
  ]
| /4 width=5 by frees_inv_gref, eq_push_inv_isid, isid_inv_eq_repl, eq_trans/
| #f1 #f2 #f #p #I #L #V #T #_ #_ #Hf #IHV #IHT #g #H elim (frees_inv_bind … H) -H
  #g1 #g2 #HV #HT #Hg @(sor_mono … Hf) -Hf
  /5 width=3 by sor_eq_repl_fwd2, sor_eq_repl_fwd1, tl_eq_repl/ (**) (* full auto too slow *)
| #f1 #f2 #f #I #L #V #T #_ #_ #Hf #IHV #IHT #g #H elim (frees_inv_flat … H) -H
  #g1 #g2 #HV #HT #Hg @(sor_mono … Hf) -Hf
  /4 width=3 by sor_eq_repl_fwd2, sor_eq_repl_fwd1/ (**) (* full auto too slow *)
]
qed-.
