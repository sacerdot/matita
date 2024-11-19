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
include "explicit_updating/syntax/term_valid_flat.ma".
include "explicit_updating/syntax/unwind_valid.ma".
include "explicit_updating/syntax/beta_valid.ma".
include "explicit_updating/reduction/xbeta1.ma".
include "explicit_updating/reduction/xbeta.ma".

(* β-REDUCTION STEP *********************************************************)

(* Destructions with term_valid *********************************************)

lemma xbeta_des_valid_false (t0) (t1):
      (𝛃′ t0 t1) → ⓕ ⊢ t0 →
      ∃∃t2. (𝛃ⓣ) t2 t1 & ⓕ ⊢ t1 & ⓣ ⊢ t2 & ♭t2 = t0.
#t0 #t1 * -t0 -t1
[ #f #t #x #y #Hx #Hy #Ht
  @(ex4_intro … x)
  [ /2 width=4 by xbeta1_unwind/
  | lapply (term_valid_eq_repl_bck … Ht … Hx) -x #H0
    lapply (term_valid_inv_lift … H0) -H0 #Ht
    /3 width=3 by unwind_valid, term_valid_eq_repl_fwd/
  | /2 width=1 by term_valid_false/
  | /2 width=1 by term_valid_inv_false_eq_flat_refl/
  ]
| #b #v #t #x #y #Hx #Hy #Ht
  elim (term_eq_inv_appl_sx … Hx) -Hx #v0 #x0 #Hv0 #Hx #H0 destruct
  elim (term_eq_inv_abst_sx … Hx) -Hx #t0 #Ht0 #H0 destruct
  lapply (beta_eq_repl (𝟎) (𝟎) … Hv0 … Ht0) -Hv0 -Ht0 // #H0
  lapply (term_eq_canc_sx … H0 … Hy) -v -t #Hy
  elim (term_valid_inv_appl_false … Ht) -Ht #Hv #H0
  lapply (term_valid_inv_abst … H0) -H0 * #Ht #H0 destruct
   @(ex4_intro … (＠v0.𝛌ⓣ.t0))
  [ /2 width=4 by xbeta1_beta/
  | /3 width=3 by beta_valid, term_valid_eq_repl_fwd/
  | /3 width=1 by term_valid_false, term_valid_beta/
  | <term_flat_appl <term_flat_abst
    >(term_valid_inv_false_eq_flat_refl … Hv)
    >(term_valid_inv_false_eq_flat_refl … Ht)
    //
  ]
]
qed-.
