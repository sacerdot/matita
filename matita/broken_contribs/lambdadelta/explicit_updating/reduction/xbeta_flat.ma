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

include "explicit_updating/syntax/term_flat_eq.ma".
include "explicit_updating/syntax/unwind_flat.ma".
include "explicit_updating/syntax/beta_flat.ma".
include "explicit_updating/reduction/xbeta.ma".
include "explicit_updating/reduction/xbeta1.ma".

(* β-REDUCTION STEP *********************************************************)

(* Constructions witth xbeta1 and term_flat *********************************)

lemma xbeta_flat: flattenable (𝛃′) (𝛃ⓕ).
#t1 #t2 * -t1 -t2
[ #f #t #x #y #Hx #Hy
  lapply (term_flat_eq_repl … Hx) -Hx <term_flat_lift #Hx
  lapply (term_flat_eq_repl … Hy) -Hy #Hy
  lapply (term_eq_trans … (unwind_flat …) … Hy) -Hy #Hy
  /2 width=4 by xbeta1_unwind/
| #b #v #t #x #y #Hx #Hy
  lapply (term_flat_eq_repl … Hx) -Hx <term_flat_appl <term_flat_abst #Hx
  lapply (term_flat_eq_repl … Hy) -Hy #Hy
  lapply (term_eq_trans … (beta_flat …) … Hy) -Hy #Hy
  /2 width=4 by xbeta1_beta/
]
qed.

(* Inversions with xbeta1 and term_flat *************************************)

lemma xbeta1_false_inv_flat_sx_aux (u1) (u2) (t1):
      (𝛃ⓕ) u1 u2 → ♭t1 = u1 →
      ∃∃t2. (𝛃′) t1 t2 & ♭t2 ≐ u2.
#u1 #u2 #t1 * -u1 -u2
[ #f #u #x #y #Hx #Hy #H0 destruct
  elim (term_eq_inv_lift_flat … Hx) -Hx #g #t #Hfg #Hut #H0 destruct
  @(ex2_intro … (▼[g]t))
  [ /2 width=4 by xbeta_unwind/
  | @(term_eq_canc_sx … Hy) -Hy
    /3 width=3 by unwind_eq_repl, unwind_flat, term_eq_trans/
  ]
| #w #u #x #y #Hx #Hy #H0 destruct
  elim (term_eq_inv_appl_flat … Hx) -Hx #v #z #Hvw #Hz #H0 destruct
  elim (term_eq_inv_abst_flat … Hz) -Hz #b #t #_ #Hut #H0 destruct
  @(ex2_intro … (⬕[𝟎←v]t))
  [ /2 width=5 by xbeta_beta/
  | @(term_eq_canc_sx … Hy) -Hy
    /3 width=3 by beta_eq_repl, beta_flat, term_eq_trans/
  ]
qed-.
