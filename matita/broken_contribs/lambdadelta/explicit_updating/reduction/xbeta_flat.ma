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
