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
include "ground/relocation/rtmap_uni.ma".
include "ground/relocation/rtmap_after.ma".

(* RELOCATION MAP ***********************************************************)

(* Properties on isuni ******************************************************)

lemma after_isid_isuni: ∀f1,f2. 𝐈❪f2❫ → 𝐔❪f1❫ → f1 ⊚ ↑f2 ≘ ↑f1.
#f1 #f2 #Hf2 #H elim H -H
/5 width=7 by after_isid_dx, after_eq_repl_back2, after_next, after_push, eq_push_inv_isid/
qed.

lemma after_uni_next2: ∀f2. 𝐔❪f2❫ → ∀f1,f. ↑f2 ⊚ f1 ≘ f → f2 ⊚ ↑f1 ≘ f.
#f2 #H elim H -f2
[ #f2 #Hf2 #f1 #f #Hf
  elim (after_inv_nxx … Hf) -Hf [2,3: // ] #g #Hg #H0 destruct
  /4 width=7 by after_isid_inv_sn, after_isid_sn, after_eq_repl_back0, eq_next/
| #f2 #_ #g2 #H2 #IH #f1 #f #Hf
  elim (after_inv_nxx … Hf) -Hf [2,3: // ] #g #Hg #H0 destruct
  /3 width=5 by after_next/
]
qed.

(* Properties on uni ********************************************************)

lemma after_uni: ∀n1,n2. 𝐔❨n1❩ ⊚ 𝐔❨n2❩ ≘ 𝐔❨n2+n1❩.
#n1 @(nat_ind_succ … n1) -n1
/3 width=5 by after_isid_sn, after_next, eq_f/
qed.

lemma after_uni_sn_pushs (m) (f): 𝐔❨m❩ ⊚ f ≘ ↑*[m]f.
#m @(nat_ind_succ … m) -m
/2 width=5 by after_isid_sn, after_next/
qed.

(* Properties with at *******************************************************)

lemma after_uni_succ_dx: ∀i2,i1,f2. @❪i1, f2❫ ≘ i2 →
                         ∀f. f2 ⊚ 𝐔❨i1❩ ≘ f → 𝐔❨i2❩ ⊚ ⫱*[i2] f2 ≘ f.
#i2 elim i2 -i2
[ #i1 #f2 #Hf2 #f #Hf
  elim (at_inv_xxp … Hf2) -Hf2 // #g2 #H1 #H2 destruct
  elim (after_inv_pnx … Hf) -Hf [ |*: // ] #g #Hg #H
  lapply (after_isid_inv_dx … Hg ?) -Hg
  /4 width=5 by after_isid_sn, after_eq_repl_back0, after_next/
| #i2 #IH #i1 #f2 #Hf2 #f #Hf >nsucc_inj
  elim (at_inv_xxn … Hf2) -Hf2 [1,3: * |*: // ]
  [ #g2 #j1 #Hg2 #H1 #H2 destruct >nsucc_inj in Hf; #Hf
    elim (after_inv_pnx … Hf) -Hf [ |*: // ] #g #Hg #H destruct
    <tls_xn /3 width=5 by after_next/
  | #g2 #Hg2 #H2 destruct
    elim (after_inv_nxx … Hf) -Hf [2,3: // ] #g #Hg #H destruct
    <tls_xn /3 width=5 by after_next/
  ]
]
qed.

lemma after_uni_succ_sn: ∀i2,i1,f2. @❪i1, f2❫ ≘ i2 →
                         ∀f. 𝐔❨i2❩ ⊚ ⫱*[i2] f2 ≘ f → f2 ⊚ 𝐔❨i1❩ ≘ f.
#i2 elim i2 -i2
[ #i1 #f2 #Hf2 #f #Hf
  elim (at_inv_xxp … Hf2) -Hf2 // #g2 #H1 #H2 destruct
  elim (after_inv_nxx … Hf) -Hf [ |*: // ] #g #Hg #H destruct
  lapply (after_isid_inv_sn … Hg ?) -Hg
  /4 width=7 by after_isid_dx, after_eq_repl_back0, after_push/
| #i2 #IH #i1 #f2 #Hf2 #f >nsucc_inj #Hf
  elim (after_inv_nxx … Hf) -Hf [2,3: // ] #g #Hg #H destruct
  elim (at_inv_xxn … Hf2) -Hf2 [1,3: * |*: // ]
  [ #g2 #j1 #Hg2 #H1 #H2 destruct <tls_xn in Hg; /3 width=7 by after_push/
  | #g2 #Hg2 #H2 destruct <tls_xn in Hg; /3 width=5 by after_next/
  ]
]
qed-.

lemma after_uni_one_dx: ∀f2,f. ⫯f2 ⊚ 𝐔❨𝟏❩ ≘ f → 𝐔❨𝟏❩ ⊚ f2 ≘ f.
#f2 #f #H @(after_uni_succ_dx … (⫯f2)) /2 width=3 by at_refl/
qed.

lemma after_uni_one_sn: ∀f1,f. 𝐔❨𝟏❩ ⊚ f1 ≘ f → ⫯f1 ⊚ 𝐔❨𝟏❩ ≘ f.
/3 width=3 by after_uni_succ_sn, at_refl/ qed-.
