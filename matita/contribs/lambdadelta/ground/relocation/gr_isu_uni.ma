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

include "ground/relocation/gr_isi_uni.ma".
include "ground/relocation/gr_isu.ma".

(* UNIFORMITY CONDITION FOR GENERIC RELOCATION MAPS *************************)

(* Constructions with gr_uni ************************************************)

(*** isuni_uni *)
lemma gr_isu_uni (n): 𝐔❪𝐮❨n❩❫.
#n @(nat_ind_succ … n) -n
/3 width=3 by gr_isu_isi, gr_isu_next/
qed.

(*** uni_inv_isuni *)
lemma gr_isu_eq_repl_back:
      gr_eq_repl_back … gr_isu.
#f1 #H elim H -f1
[ /3 width=3 by gr_isu_isi, gr_isi_eq_repl_back/
| #f1 #_ #g1 * #IH #f2 #H -g1
  elim (gr_eq_inv_next_sn … H) -H
  /3 width=3 by gr_isu_next/
]
qed-.

lemma gr_isu_eq_repl_fwd:
      gr_eq_repl_fwd … gr_isu.
/3 width=3 by gr_isu_eq_repl_back, gr_eq_repl_sym/ qed-.

(* Inversions with gr_uni ***************************************************)

(*** uni_isuni *)
lemma gr_isu_inv_uni (f): 𝐔❪f❫ → ∃n. 𝐮❨n❩ ≡ f.
#f #H elim H -f
[ /3 width=2 by gr_isi_inv_uni, ex_intro/
| #f #_ #g #H * /3 width=6 by gr_eq_next, ex_intro/
]
qed-.
