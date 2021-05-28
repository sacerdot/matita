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

include "ground/relocation/gr_tl_eq_eq.ma".
include "ground/relocation/gr_isd.ma".

(* DIVERGENCE CONDITION FOR GENERIC RELOCATION MAPS ***********************************************************)

(* Properties with gr_eq *********************************************************)

(*** isdiv_eq_repl_back *)
corec lemma gr_isd_eq_repl_back:
            gr_eq_repl_back … gr_isd.
#f1 #H cases (gr_isd_inv_gen … H) -H
#g1 #Hg1 #H1 #f2 #Hf cases (gr_eq_inv_next_sn … Hf … H1) -f1
/3 width=3 by gr_isd_next/
qed-.

(*** isdiv_eq_repl_fwd *)
lemma gr_isd_eq_repl_fwd:
      gr_eq_repl_fwd … gr_isd.
/3 width=3 by gr_isd_eq_repl_back, gr_eq_repl_sym/ qed-.

(* Main inversion lemmas with gr_eq ***************)

(*** isdiv_inv_eq_repl *)
corec theorem gr_isd_inv_eq_repl (g1) (g2): 𝛀❪g1❫ → 𝛀❪g2❫ → g1 ≡ g2.
#H1 #H2
cases (gr_isd_inv_gen … H1) -H1
cases (gr_isd_inv_gen … H2) -H2
/3 width=5 by gr_eq_next/
qed-.

(* Alternative definition with gr_eq ***************************************************)

(*** eq_next_isdiv *)
corec lemma gr_eq_next_isd (f): ↑f ≡ f → 𝛀❪f❫.
#H cases (gr_eq_inv_next_sn … H) -H
/4 width=3 by gr_isd_next, gr_eq_trans/
qed.

(*** eq_next_inv_isdiv *)
corec lemma gr_eq_next_inv_isd (g): 𝛀❪g❫ → ↑g ≡ g.
* -g #f #g #Hf *
/3 width=5 by gr_eq_next/
qed-.
