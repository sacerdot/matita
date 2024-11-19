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
include "explicit_updating/syntax/term_valid.ma".

(* VALIDITY FOR TERM ********************************************************)

(* Constructions with term_eq ***********************************************)

lemma term_valid_eq_repl_fwd (b):
      replace_1_fwd … term_eq (term_valid b).
#b #t1 #H0 elim H0 -t1
[ #p #y #Hy
  lapply (term_eq_inv_lref_sx … Hy) -Hy #H0 destruct //
| #t1 #_ #IH #y #Hy
  elim (term_eq_inv_abst_sx … Hy) -Hy #t2 #Ht12 #H0 destruct
  /3 width=1 by term_valid_abst/
| #v1 #t1 #_ #_ #IHv #IHt #y #Hy
  elim (term_eq_inv_appl_sx … Hy) -Hy #v2 #t2 #Hv12 #Ht12 #H0 destruct
  /3 width=1 by term_valid_appl/
| #f1 #t1 #_ #IH #y #Hy
  elim (term_eq_inv_lift_sx … Hy) -Hy #f2 #t2 #_ #Ht12 #H0 destruct
  /3 width=1 by term_valid_lift/
| #v1 #t1 #_ #_ #IHv #IHt #y #Hy
  elim (term_eq_inv_appl_sx … Hy) -Hy #v2 #y2 #Hv12 #Hy2 #H0 destruct
  elim (term_eq_inv_abst_sx … Hy2) -Hy2 #t2 #Ht12 #H0 destruct
  /3 width=1 by term_valid_beta/
]
qed-.

lemma term_valid_eq_repl_bck (b):
      replace_1_back … term_eq (term_valid b).
/3 width=3 by term_valid_eq_repl_fwd, term_eq_sym/
qed-.
