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

include "ground/relocation/gr_tls.ma".
include "ground/relocation/gr_nat.ma".
include "ground/relocation/gr_isi_uni.ma".
include "ground/relocation/gr_after_isi.ma".

(* RELATIONAL COMPOSITION FOR GENERIC RELOCATION MAPS ***********************************************************)

(* Properties with gr_nat and uni *)

(*** after_uni_dx *)
lemma gr_after_nat_uni (l2) (l1):
      ∀f2. @↑❪l1, f2❫ ≘ l2 →
      ∀f. f2 ⊚ 𝐮❨l1❩ ≘ f → 𝐮❨l2❩ ⊚ ⫱*[l2] f2 ≘ f.
#l2 @(nat_ind_succ … l2) -l2
[ #l1 #f2 #Hf2 #f #Hf
  elim (gr_nat_inv_zero_dx … Hf2) -Hf2 // #g2 #H1 #H2 destruct
  lapply (gr_after_isi_inv_dx … Hf ?) -Hf
  /3 width=3 by gr_after_isi_sn, gr_after_eq_repl_back/
| #l2 #IH #l1 #f2 #Hf2 #f #Hf
  elim (gr_nat_inv_succ_dx … Hf2) -Hf2 [1,3: * |*: // ]
  [ #g2 #k1 #Hg2 #H1 #H2 destruct
    elim (gr_after_inv_push_next … Hf) -Hf [ |*: // ] #g #Hg #H destruct
    <gr_tls_swap /3 width=5 by gr_after_next/
  | #g2 #Hg2 #H2 destruct
    elim (gr_after_inv_next_sn … Hf) -Hf [ |*: // ] #g #Hg #H destruct
    <gr_tls_swap /3 width=5 by gr_after_next/
  ]
]
qed.

(*** after_uni_sn *)
lemma gr_nat_after_uni_tls (l2) (l1):
      ∀f2. @↑❪l1, f2❫ ≘ l2 →
      ∀f. 𝐮❨l2❩ ⊚ ⫱*[l2] f2 ≘ f → f2 ⊚ 𝐮❨l1❩ ≘ f.
#l2 @(nat_ind_succ … l2) -l2
[ #l1 #f2 #Hf2 #f #Hf
  elim (gr_nat_inv_zero_dx … Hf2) -Hf2 // #g2 #H1 #H2 destruct
  lapply (gr_after_isi_inv_sn … Hf ?) -Hf
  /3 width=3 by gr_after_isi_dx, gr_after_eq_repl_back/
| #l2 #IH #l1 #f2 #Hf2 #f #Hf
  elim (gr_after_inv_next_sn … Hf) -Hf [2,3: // ] #g #Hg #H destruct
  elim (gr_nat_inv_succ_dx … Hf2) -Hf2 [1,3: * |*: // ]
  [ #g2 #k1 #Hg2 #H1 #H2 destruct /3 width=7 by gr_after_push/
  | #g2 #Hg2 #H2 destruct /3 width=5 by gr_after_next/
  ]
]
qed-.
