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

include "delayed_updating/computation/prototerm_dbf_c_residuals_eq.ma".
include "delayed_updating/computation/prototerm_ins_dbf_residuals_eq.ma".
include "delayed_updating/computation/prototerm_ins_dbf_c_residuals.ma".
include "delayed_updating/computation/dbf_steps.ma".
include "delayed_updating/computation/dbf_dsteps_eq.ma".

(* DELAYED BALANCED FOCUSED COMPUTATION IN A DEVELOPMENT ********************)

(* Constructions with dbfss *************************************************)

lemma dbfss_dbfdss (t1) (t2) (rs):
      t1 ➡*𝐝𝐛𝐟[rs] t2 → ∀u. rs ϵ* u →
      t1 Ꟈ➡*𝐝𝐛𝐟[u, u /𝐝𝐛𝐟 rs] t2.
#t1 #t2 #rs #Ht12 @(dbfss_ind_sx … Ht12) -t1 -rs
[ #x1 #x2 #rs #Hx12 #IH #u #Hrs
  @(eq_dbfdss_trans … (IH …)) //
| /2 width=1 by dbfdss_refl/
| #t1 #t0 #rs #r #Ht10 #_ #IH #u * #Hr #Hrs
  <term_dbfrs_lcons
  /3 width=4 by dbfdss_step_sx, dbfds_mk/
]
qed.

(* Inversions with dbfss ****************************************************)

lemma dbfdss_inv_dbfss (t1) (t2) (u1) (u2):
      t1 Ꟈ➡*𝐝𝐛𝐟[u1,u2] t2 →
      ∃∃rs. t1 ➡*𝐝𝐛𝐟[rs] t2 & rs ϵ* u1 & u1 /𝐝𝐛𝐟 rs ⇔ u2.
#t1 #t2 #u1 #u2 #H12 elim H12 -t1 -t2 -u1 -u2
[ #t1 #t2 #u1 #u2 #Ht12 #Hu12
  /3 width=4 by frs_refl, ex3_intro/
| #t1 #t2 #u1 #u2 * #r #Hr #Ht12 #Hu12
  /3 width=4 by frs_step, term_ins_dbfr_lcons, ex3_intro/
| #t #t1 #t2 #u #u1 #u2 #_ #_ * #rs1 #Ht1 #Hrs1 #Hu1 * #rs2 #Ht2 #Hrs2 #Hu2
  @(ex3_intro … (rs1⨁rs2))
  [ /2 width=3 by frs_trans/
  | /4 width=3 by term_ins_dbfr_eq_repl_fwd, term_ins_dbfr_append, subset_eq_sym/
  | <term_dbfrs_append
    @(subset_eq_trans … Hu2) -u2
    @(term_dbfrs_eq_repl_fwd … Hu1)
  ]
]
qed-.
