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
include "explicit_updating/reduction/xbeta1.ma".
include "explicit_updating/reduction/xbeta.ma".

(* β-REDUCTION STEP *********************************************************)

(* Inversions with xbeta1 ***************************************************)

lemma xbeta_inv_beta1_false (t1) (t2):
      (𝛃′) t1 t2 → ⓕ ⊢ t1 → (𝛃ⓕ) t1 t2.
#t1 #t2 * -t1 -t2
[ /2 width=4 by xbeta1_unwind/
| #b #v #t #x #y #Hx #Hy #H0
  lapply (term_valid_eq_repl_bck … H0 … Hx) -H0 #H0
  elim (term_valid_inv_appl_false … H0) -H0 #_ #H0
  elim (term_valid_inv_abst … H0) -H0 #_ #H0 destruct
  /2 width=4 by xbeta1_beta/
]
qed.
