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

include "ground/relocation/pr_tl_eq_eq.ma".
include "ground/relocation/pr_isd.ma".

(* DIVERGENCE CONDITION FOR PARTIAL RELOCATION MAPS *************************)

(* Constructions with pr_eq *************************************************)

(*** isdiv_eq_repl_back *)
corec lemma pr_isd_eq_repl_back:
            pr_eq_repl_back … pr_isd.
#f1 #H cases (pr_isd_inv_gen … H) -H
#g1 #Hg1 #H1 #f2 #Hf cases (pr_eq_inv_next_sn … Hf … H1) -f1
/3 width=3 by pr_isd_next/
qed-.

(*** isdiv_eq_repl_fwd *)
lemma pr_isd_eq_repl_fwd:
      pr_eq_repl_fwd … pr_isd.
/3 width=3 by pr_isd_eq_repl_back, pr_eq_repl_sym/ qed-.

(* Main inversions with pr_eq ***********************************************)

(*** isdiv_inv_eq_repl *)
corec theorem pr_isd_inv_eq_repl (g1) (g2): 𝛀❨g1❩ → 𝛀❨g2❩ → g1 ≐ g2.
#H1 #H2
cases (pr_isd_inv_gen … H1) -H1
cases (pr_isd_inv_gen … H2) -H2
/3 width=5 by pr_eq_next/
qed-.

(* Alternative definition with pr_eq ****************************************)

(*** eq_next_isdiv *)
corec lemma pr_eq_next_isd (f): ↑f ≐ f → 𝛀❨f❩.
#H cases (pr_eq_inv_next_sn … H) -H
/4 width=3 by pr_isd_next, pr_eq_trans/
qed.

(*** eq_next_inv_isdiv *)
corec lemma pr_eq_next_inv_isd (g): 𝛀❨g❩ → ↑g ≐ g.
* -g #f #g #Hf *
/3 width=5 by pr_eq_next/
qed-.
