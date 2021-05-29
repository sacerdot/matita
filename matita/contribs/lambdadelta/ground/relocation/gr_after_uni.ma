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

include "ground/arith/nat_plus.ma".
(* * it should not depend on gr_isi *)
include "ground/relocation/gr_isi_uni.ma".
include "ground/relocation/gr_after_isi.ma".

(* RELATIONAL COMPOSITION FOR GENERIC RELOCATION MAPS ***********************)

(* Constructions with gr_uni ************************************************)

(*** after_uni *)
lemma gr_after_uni (h1) (h2): 𝐮❨h1❩ ⊚ 𝐮❨h2❩ ≘ 𝐮❨h2+h1❩.
#h1 @(nat_ind_succ … h1) -h1
/3 width=5 by gr_after_isi_sn, gr_after_next, eq_f/
qed.

(*** after_uni_sn_pushs *)
lemma gr_after_uni_sn_pushs (h):
      ∀f. 𝐮❨h❩ ⊚ f ≘ ↑*[h]f.
#h @(nat_ind_succ … h) -h
/2 width=5 by gr_after_isi_sn, gr_after_next/
qed.

lemma gr_after_uni_isi_next (h1):
      ∀f2. 𝐈❪f2❫ → 𝐮❨h1❩ ⊚ ↑f2 ≘ ↑𝐮❨h1❩.
#h1 @(nat_ind_succ … h1) -h1
/5 width=7 by gr_after_isi_dx, gr_after_eq_repl_back_sn, gr_after_next, gr_after_push, gr_isi_inv_eq_push/
qed.

lemma gr_after_uni_next_sn (h2):
      ∀f1,f. ↑𝐮❨h2❩ ⊚ f1 ≘ f → 𝐮❨h2❩ ⊚ ↑f1 ≘ f.
#h2 @(nat_ind_succ … h2) -h2
[ #f1 #f #Hf
  elim (gr_after_inv_next_sn … Hf) -Hf [2,3: // ] #g #Hg #H0 destruct
  /4 width=7 by gr_after_isi_inv_sn, gr_after_isi_sn, gr_after_eq_repl_back, gr_eq_next/
| #h2 #IH #f1 #f #Hf
  elim (gr_after_inv_next_sn … Hf) -Hf [2,3: // ] #g #Hg #H0 destruct
  /3 width=5 by gr_after_next/
]
qed.
