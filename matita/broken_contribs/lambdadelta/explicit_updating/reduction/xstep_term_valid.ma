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

include "ground/arith/pnat_lt_plus.ma".
include "ground/arith/wf1_ind_plt.ma".
include "explicit_updating/syntax/term_weight.ma".
include "explicit_updating/syntax/term_valid_eq.ma".
include "explicit_updating/reduction/xstep_term.ma".

(* X-REDUCTION FOR TERM *****************************************************)

(* Constructions with valid_term ********************************************)

lemma term_valid_xstep_trans (R) (c):
      (∀t1,t2. R (𝛌ⓣ.t1) t2 → ⊥) →
      (∀t1,t2. R t1 t2 → c ⊢ t1 → c ⊢ t2) →
      ∀t1,t2. t1 ➡[R] t2 → c ⊢ t1 → c ⊢ t2.
#R #c #H1R #H2R #t
@(wf1_ind_plt … term_weight … t) -t #q #IH #t #H0 #x2 destruct
@(insert_eq_1 … t) #x1 * -x1 -x2
[ #t1 #t2 #Ht12 #Ht #Ht1 destruct -IH
  /2 width=3/
| #b #t1 #t2 #Ht12 #Ht #H0 destruct
  elim (term_valid_inv_abst … H0) -H0 #Ht1 #H0 destruct
  /3 width=4 by term_valid_abst/
| #v1 #v2 #t1 #t2 #Hv12 #Ht12 #Ht #H0 destruct
  elim (term_valid_inv_appl … H0) -H0 *
  [ #Hv1 #Ht1
    /3 width=4 by term_valid_eq_repl_fwd, term_valid_appl/
  | #x1 #Hv1 #Hx1 #H1 #H2 destruct
    elim (term_eq_inv_abst_sx … Ht12) -Ht12 #x2 #Hx12 #H0 destruct
    /3 width=4 by term_valid_eq_repl_fwd, term_valid_beta/
  ]
| #v1 #v2 #t1 #t2 #Hv12 #Ht12 #Ht #H0 destruct
  elim (term_valid_inv_appl … H0) -H0 *
  [ #Hv1 #Ht1
    /3 width=4 by term_valid_eq_repl_fwd, term_valid_appl/
  | #x1 #Hv1 #Hx1 #H1 #H2 destruct
    elim (xstep_term_inv_abst_sx … Ht12) -Ht12
    [ #H0 elim (H1R … H0)
    | * #x2 #Hx12 #H0 destruct
      /3 width=4 by term_valid_eq_repl_fwd, term_valid_beta/
    ]
  ]
| #f1 #f2 #t1 #t2 #_ #Ht12 #Ht #H0 destruct
  lapply (term_valid_inv_lift … H0) -H0 #Ht1
  /3 width=4 by term_valid_lift/
]
qed.
