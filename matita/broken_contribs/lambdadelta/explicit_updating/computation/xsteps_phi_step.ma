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

include "explicit_updating/reduction/xstep_phi.ma".
include "explicit_updating/computation/xsteps_phi.ma".

(* X-COMPUTATION TO ♭-NORMAL FORM *******************************************)

(* Constructions with xstep_phi *********************************************)

lemma xsteps_phi_step_dx (t) (t1) (t2):
      t1 ➡*[𝛃ⓣ] t → t ➡𝛟 t2 → t1 ➡*𝛟 t2.
#t0 #t1 #t2 #Ht10 * #Ht02 #Ht2
/3 width=3 by xsteps_dx, xsteps_phi_fold/
qed.

lemma xsteps_phi_step (t1) (t2):
      t1 ➡𝛟 t2 → t1 ➡*𝛟 t2.
/3 width=3 by xsteps_refl, xsteps_phi_step_dx/
qed.
