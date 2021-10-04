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
include "ground/relocation/pr_isi.ma".

(* IDENTITY CONDITION FOR PARTIAL RELOCATION MAPS ***************************)

(* Constructions with pr_eq *************************************************)

(*** isid_eq_repl_back *)
corec lemma pr_isi_eq_repl_back:
            pr_eq_repl_back … pr_isi.
#f1 #H
cases (pr_isi_inv_gen … H) -H #g1 #Hg1 #H1 #f2 #Hf
cases (pr_eq_inv_push_sn … Hf … H1) -f1
/3 width=3 by pr_isi_push/
qed-.

(*** isid_eq_repl_fwd *)
lemma pr_isi_eq_repl_fwd:
      pr_eq_repl_fwd … pr_isi.
/3 width=3 by pr_isi_eq_repl_back, pr_eq_repl_sym/ qed-.

(* Main inversions with pr_eq ***********************************************)

(*** isid_inv_eq_repl *)
corec theorem pr_isi_inv_eq_repl (g1) (g2): 𝐈❪g1❫ → 𝐈❪g2❫ → g1 ≡ g2.
#H1 #H2
cases (pr_isi_inv_gen … H1) -H1
cases (pr_isi_inv_gen … H2) -H2
/3 width=5 by pr_eq_push/
qed-.

(* Alternative definition with pr_eq ****************************************)

(*** eq_push_isid *)
corec lemma pr_eq_push_isi (f): ⫯f ≡ f → 𝐈❪f❫.
#H cases (pr_eq_inv_push_sn … H) -H
/4 width=3 by pr_isi_push, pr_eq_trans/
qed.

(*** eq_push_inv_isid *)
corec lemma pr_isi_inv_eq_push (g): 𝐈❪g❫ → ⫯g ≡ g.
* -g #f #g #Hf *
/3 width=5 by pr_eq_push/
qed-.
