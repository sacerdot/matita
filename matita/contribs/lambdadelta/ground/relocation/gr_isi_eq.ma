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
include "ground/relocation/gr_isi.ma".

(* IDENTITY CONDITION FOR GENERIC RELOCATION MAPS ***************************)

(* Constructions with gr_eq *************************************************)

(*** isid_eq_repl_back *)
corec lemma gr_isi_eq_repl_back:
            gr_eq_repl_back … gr_isi.
#f1 #H
cases (gr_isi_inv_gen … H) -H #g1 #Hg1 #H1 #f2 #Hf
cases (gr_eq_inv_push_sn … Hf … H1) -f1
/3 width=3 by gr_isi_push/
qed-.

(*** isid_eq_repl_fwd *)
lemma gr_isi_eq_repl_fwd:
      gr_eq_repl_fwd … gr_isi.
/3 width=3 by gr_isi_eq_repl_back, gr_eq_repl_sym/ qed-.

(* Main inversions with gr_eq ***********************************************)

(*** isid_inv_eq_repl *)
corec theorem gr_isi_inv_eq_repl (g1) (g2): 𝐈❪g1❫ → 𝐈❪g2❫ → g1 ≡ g2.
#H1 #H2
cases (gr_isi_inv_gen … H1) -H1
cases (gr_isi_inv_gen … H2) -H2
/3 width=5 by gr_eq_push/
qed-.

(* Alternative definition with gr_eq ****************************************)

(*** eq_push_isid *)
corec lemma gr_eq_push_isi (f): ⫯f ≡ f → 𝐈❪f❫.
#H cases (gr_eq_inv_push_sn … H) -H
/4 width=3 by gr_isi_push, gr_eq_trans/
qed.

(*** eq_push_inv_isid *)
corec lemma gr_isi_inv_eq_push (g): 𝐈❪g❫ → ⫯g ≡ g.
* -g #f #g #Hf *
/3 width=5 by gr_eq_push/
qed-.
