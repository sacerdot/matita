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

include "ground/relocation/rtmap_uni.ma".
include "ground/relocation/rtmap_nat.ma".
include "ground/relocation/rtmap_after.ma".

(* RELOCATION MAP ***********************************************************)

lemma after_uni_dx: ∀l2,l1,f2. @↑❪l1, f2❫ ≘ l2 →
                    ∀f. f2 ⊚ 𝐔❨l1❩ ≘ f → 𝐔❨l2❩ ⊚ ⫱*[l2] f2 ≘ f.
#l2 @(nat_ind_succ … l2) -l2
[ #l1 #f2 #Hf2 #f #Hf
  elim (rm_nat_inv_xxp … Hf2) -Hf2 // #g2 #H1 #H2 destruct
  lapply (after_isid_inv_dx … Hf ?) -Hf
  /3 width=3 by after_isid_sn, after_eq_repl_back0/
| #l2 #IH #l1 #f2 #Hf2 #f #Hf
  elim (rm_nat_inv_xxn … Hf2) -Hf2 [1,3: * |*: // ]
  [ #g2 #k1 #Hg2 #H1 #H2 destruct
    elim (after_inv_pnx … Hf) -Hf [ |*: // ] #g #Hg #H destruct
    <tls_xn /3 width=5 by after_next/
  | #g2 #Hg2 #H2 destruct
    elim (after_inv_nxx … Hf) -Hf [ |*: // ] #g #Hg #H destruct
    <tls_xn /3 width=5 by after_next/
  ]
]
qed.

lemma after_uni_sn: ∀l2,l1,f2. @↑❪l1, f2❫ ≘ l2 →
                    ∀f. 𝐔❨l2❩ ⊚ ⫱*[l2] f2 ≘ f → f2 ⊚ 𝐔❨l1❩ ≘ f.
#l2 @(nat_ind_succ … l2) -l2
[ #l1 #f2 #Hf2 #f #Hf
  elim (rm_nat_inv_xxp … Hf2) -Hf2 // #g2 #H1 #H2 destruct
  lapply (after_isid_inv_sn … Hf ?) -Hf
  /3 width=3 by after_isid_dx, after_eq_repl_back0/
| #l2 #IH #l1 #f2 #Hf2 #f #Hf
  elim (after_inv_nxx … Hf) -Hf [2,3: // ] #g #Hg #H destruct
  elim (rm_nat_inv_xxn … Hf2) -Hf2 [1,3: * |*: // ]
  [ #g2 #k1 #Hg2 #H1 #H2 destruct /3 width=7 by after_push/
  | #g2 #Hg2 #H2 destruct /3 width=5 by after_next/
  ]
]
qed-.

