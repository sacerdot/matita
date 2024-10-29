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

include "explicit_updating/syntax/term_eq.ma".
include "explicit_updating/syntax/term_flat.ma".

(* FLATTENING FOR TERM ******************************************************)

(* Constructions with term_eq ***********************************************)

lemma term_flat_eq_repl:
      compatible_2_fwd … term_eq term_eq term_flat.
#t1 #t2 #Ht elim Ht -t1 -t2
/2 width=1 by term_eq_abst, term_eq_appl, term_eq_lift/
qed.

(* Inversions with term_eq **************************************************)

lemma term_eq_inv_lref_flat (p) (y):
      (𝛏p) ≐ ♭y → 𝛏p = y.
#p #y #Hy
/3 width=1 by eq_inv_lref_flat, term_eq_inv_lref_sx/
qed-.

lemma term_eq_inv_abst_flat (b1) (t1) (y):
      (𝛌b1.t1) ≐ ♭y →
      ∃∃b2,t2. ⓕ = b1 & t1 ≐ ♭t2 & 𝛌b2.t2 = y.
#b1 #t1 #y #Hy
elim (term_eq_inv_abst_sx  … Hy) -Hy #t2 #Ht12 #Hy
elim (eq_inv_abst_flat … Hy) -Hy #b2 #u2 #H1 #H2 #H3 destruct
/2 width=5 by ex3_2_intro/
qed-.

lemma term_eq_inv_appl_flat (v1) (t1) (y):
      (＠v1.t1) ≐ ♭y →
      ∃∃v2,t2. v1 ≐ ♭v2 & t1 ≐ ♭t2 & ＠v2.t2 = y.
#v1 #t1 #y #Hy
elim (term_eq_inv_appl_sx  … Hy) -Hy #v2 #t2 #Hv12 #Ht12 #Hy
elim (eq_inv_appl_flat … Hy) -Hy #w2 #u2 #H1 #H2 #H3 destruct
/2 width=5 by ex3_2_intro/
qed-.

lemma term_eq_inv_lift_flat (f1) (t1) (y):
      (𝛗f1.t1) ≐ ♭y →
      ∃∃f2,t2. f1 ≐ f2 & t1 ≐ ♭t2 & 𝛗f2.t2 = y.
#f1 #t1 #y #Hy
elim (term_eq_inv_lift_sx  … Hy) -Hy #f2 #t2 #Hf #Ht12 #Hy
elim (eq_inv_lift_flat … Hy) -Hy #u2 #H1 #H2 destruct
/2 width=5 by ex3_2_intro/
qed-.

(* Advanced inversions with term_eq *****************************************)

lemma term_eq_inv_flat_sx_refl (t):
      ♭t ≐ t → ♭t = t.
#t elim t -t
[ //
| #b #t #IH <term_flat_abst #H0
  elim (term_eq_inv_abst_bi … H0) -H0 #H0 destruct
  /3 width=1 by eq_f/
| #v #t #IHv #IHt <term_flat_appl #H0
  elim (term_eq_inv_appl_bi … H0) -H0
  /3 width=1 by eq_f2/
| #f #t #IHt <term_flat_lift #H0
  elim (term_eq_inv_lift_bi … H0) -H0 #_
  /3 width=1 by eq_f/
]
qed-.
