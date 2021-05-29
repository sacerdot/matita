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
include "ground/relocation/gr_pat.ma".
(* * it should not depend on gr_isi *)
include "ground/relocation/gr_isi_uni.ma".
include "ground/relocation/gr_after_isi.ma".

(* RELATIONAL COMPOSITION FOR GENERIC RELOCATION MAPS ***********************)

(* Constructions with gr_pat and gr_uni and gr_tls **************************)

(*** after_uni_succ_dx *)
lemma gr_after_pat_uni (i2) (i1):
      ∀f2. @❪i1, f2❫ ≘ i2 →
      ∀f. f2 ⊚ 𝐮❨i1❩ ≘ f → 𝐮❨i2❩ ⊚ ⫱*[i2] f2 ≘ f.
#i2 elim i2 -i2
[ #i1 #f2 #Hf2 #f #Hf
  elim (gr_pat_inv_unit_dx … Hf2) -Hf2 // #g2 #H1 #H2 destruct
  elim (gr_after_inv_push_next … Hf) -Hf [ |*: // ] #g #Hg #H
  lapply (gr_after_isi_inv_dx … Hg ?) -Hg
  /4 width=5 by gr_after_isi_sn, gr_after_eq_repl_back, gr_after_next/
| #i2 #IH #i1 #f2 #Hf2 #f #Hf >nsucc_inj
  elim (gr_pat_inv_succ_dx … Hf2) -Hf2 [1,3: * |*: // ]
  [ #g2 #j1 #Hg2 #H1 #H2 destruct >nsucc_inj in Hf; #Hf
    elim (gr_after_inv_push_next … Hf) -Hf [ |*: // ] #g #Hg #H destruct
    <gr_tls_swap /3 width=5 by gr_after_next/
  | #g2 #Hg2 #H2 destruct
    elim (gr_after_inv_next_sn … Hf) -Hf [2,3: // ] #g #Hg #H destruct
    <gr_tls_swap /3 width=5 by gr_after_next/
  ]
]
qed.

(*** after_uni_succ_sn *)
lemma gr_pat_after_uni_tls (i2) (i1):
      ∀f2. @❪i1, f2❫ ≘ i2 →
      ∀f. 𝐮❨i2❩ ⊚ ⫱*[i2] f2 ≘ f → f2 ⊚ 𝐮❨i1❩ ≘ f.
#i2 elim i2 -i2
[ #i1 #f2 #Hf2 #f #Hf
  elim (gr_pat_inv_unit_dx … Hf2) -Hf2 // #g2 #H1 #H2 destruct
  elim (gr_after_inv_next_sn … Hf) -Hf [ |*: // ] #g #Hg #H destruct
  lapply (gr_after_isi_inv_sn … Hg ?) -Hg
  /4 width=7 by gr_after_isi_dx, gr_after_eq_repl_back, gr_after_push/
| #i2 #IH #i1 #f2 #Hf2 #f >nsucc_inj #Hf
  elim (gr_after_inv_next_sn … Hf) -Hf [2,3: // ] #g #Hg #H destruct
  elim (gr_pat_inv_succ_dx … Hf2) -Hf2 [1,3: * |*: // ]
  [ #g2 #j1 #Hg2 #H1 #H2 destruct <gr_tls_swap in Hg; /3 width=7 by gr_after_push/
  | #g2 #Hg2 #H2 destruct <gr_tls_swap in Hg; /3 width=5 by gr_after_next/
  ]
]
qed-.

(* Advanced constructions with gr_uni ***************************************)

(*** after_uni_one_dx *)
lemma gr_after_push_unit:
      ∀f2,f. ⫯f2 ⊚ 𝐮❨𝟏❩ ≘ f → 𝐮❨𝟏❩ ⊚ f2 ≘ f.
#f2 #f #H
@(gr_after_pat_uni … (⫯f2))
/2 width=3 by gr_pat_refl/
qed.

(*** after_uni_one_sn *)
lemma gr_after_unit_sn:
      ∀f1,f. 𝐮❨𝟏❩ ⊚ f1 ≘ f → ⫯f1 ⊚ 𝐮❨𝟏❩ ≘ f.
/3 width=3 by gr_pat_after_uni_tls, gr_pat_refl/ qed-.
