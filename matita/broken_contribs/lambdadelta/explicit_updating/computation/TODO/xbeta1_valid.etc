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

include "explicit_updating/syntax/term_valid_eq.ma".
include "explicit_updating/syntax/unwind_valid.ma".
include "explicit_updating/syntax/beta_valid.ma".
include "explicit_updating/reduction/xbeta1.ma".

(* MARKED β-REDUCTION STEP **************************************************)

(* Constructions with valid_term ********************************************)

lemma term_valid_xbeta1_trans (c) (b) (t1) (t2):
      (𝛃b) t1 t2 → c ⊢ t1 → c ⊢ t2.
#c #b #t1 #t2 * -t1 -t2
[ #f #t #x #y #Hx #Hy #H0
  lapply (term_valid_eq_repl_bck  … H0 … Hx) -x #H0
  @(term_valid_eq_repl_fwd  … Hy) -y
  lapply (term_valid_inv_lift … H0) -H0 #H0
  /2 width=1 by unwind_valid/
| #v #t #x #y #Hx #Hy #H0
  lapply (term_valid_eq_repl_bck  … H0 … Hx) -x #H0
  @(term_valid_eq_repl_fwd  … Hy) -y
  elim (term_valid_inv_appl … H0) -H0 *
  [ #Hv #H0
    elim (term_valid_inv_abst … H0) -H0 #Ht #_ -b
    /2 width=1 by beta_valid/
  | #x #v #x #H1 #H2 destruct
    /2 width=1 by beta_valid/
  ]
]
qed.
