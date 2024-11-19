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
include "explicit_updating/computation/xsteps_phi.ma".

(* X-COMPUTATION TO ♭-NORMAL FORM *******************************************)

(* Constructions with term_eq ***********************************************)

lemma xsteps_phi_eq_repl:
      replace_2 … term_eq term_eq xsteps_phi.
#t1 #t2 * #Ht12 #Ht2 #u1 #Htu1 #u2 #Htu2
lapply (xsteps_eq_repl … Ht12 … Htu1 … Htu2) -t1
[ /2 width=5 by xbeta1_eq_repl/ ] #Hu12
/3 width=3 by xsteps_phi_fold, term_valid_eq_repl_fwd/
qed-.

lemma xsteps_phi_eq_trans (t) (t1) (t2):
      t1 ➡*𝛟 t → t ≐ t2 → t1 ➡*𝛟 t2.
/2 width=5 by xsteps_phi_eq_repl/
qed-.

lemma eq_xsteps_phi_trans (t) (t1) (t2):
      t1 ≐ t → t ➡*𝛟 t2 → t1 ➡*𝛟 t2.
/3 width=5 by xsteps_phi_eq_repl, term_eq_sym/
qed-.
