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

include "ground/relocation/pr_tls.ma".
include "ground/relocation/pr_pat.ma".
(* * it should not depend on pr_isi *)
include "ground/relocation/pr_isi_uni.ma".
include "ground/relocation/pr_after_isi.ma".

(* RELATIONAL COMPOSITION FOR PARTIAL RELOCATION MAPS ***********************)

(* Constructions with pr_pat and pr_uni and pr_tls **************************)

(*** after_uni_succ_dx *)
lemma pr_after_pat_uni (i2) (i1):
      ∀f2. @❨i1, f2❩ ≘ i2 →
      ∀f. f2 ⊚ 𝐮❨i1❩ ≘ f → 𝐮❨i2❩ ⊚ ⫰*[i2] f2 ≘ f.
#i2 elim i2 -i2
[ #i1 #f2 #Hf2 #f #Hf
  elim (pr_pat_inv_unit_dx … Hf2) -Hf2 // #g2 #H1 #H2 destruct
  elim (pr_after_inv_push_next … Hf) -Hf [ |*: // ] #g #Hg #H
  lapply (pr_after_isi_inv_dx … Hg ?) -Hg
  /4 width=5 by pr_after_isi_sn, pr_after_eq_repl_back, pr_after_next/
| #i2 #IH #i1 #f2 #Hf2 #f #Hf >nsucc_inj
  elim (pr_pat_inv_succ_dx … Hf2) -Hf2 [1,3: * |*: // ]
  [ #g2 #j1 #Hg2 #H1 #H2 destruct >nsucc_inj in Hf; #Hf
    elim (pr_after_inv_push_next … Hf) -Hf [ |*: // ] #g #Hg #H destruct
    <pr_tls_swap /3 width=5 by pr_after_next/
  | #g2 #Hg2 #H2 destruct
    elim (pr_after_inv_next_sn … Hf) -Hf [2,3: // ] #g #Hg #H destruct
    <pr_tls_swap /3 width=5 by pr_after_next/
  ]
]
qed.

(*** after_uni_succ_sn *)
lemma pr_pat_after_uni_tls (i2) (i1):
      ∀f2. @❨i1, f2❩ ≘ i2 →
      ∀f. 𝐮❨i2❩ ⊚ ⫰*[i2] f2 ≘ f → f2 ⊚ 𝐮❨i1❩ ≘ f.
#i2 elim i2 -i2
[ #i1 #f2 #Hf2 #f #Hf
  elim (pr_pat_inv_unit_dx … Hf2) -Hf2 // #g2 #H1 #H2 destruct
  elim (pr_after_inv_next_sn … Hf) -Hf [ |*: // ] #g #Hg #H destruct
  lapply (pr_after_isi_inv_sn … Hg ?) -Hg
  /4 width=7 by pr_after_isi_dx, pr_after_eq_repl_back, pr_after_push/
| #i2 #IH #i1 #f2 #Hf2 #f >nsucc_inj #Hf
  elim (pr_after_inv_next_sn … Hf) -Hf [2,3: // ] #g #Hg #H destruct
  elim (pr_pat_inv_succ_dx … Hf2) -Hf2 [1,3: * |*: // ]
  [ #g2 #j1 #Hg2 #H1 #H2 destruct <pr_tls_swap in Hg; /3 width=7 by pr_after_push/
  | #g2 #Hg2 #H2 destruct <pr_tls_swap in Hg; /3 width=5 by pr_after_next/
  ]
]
qed-.

(* Advanced constructions with pr_uni ***************************************)

(*** after_uni_one_dx *)
lemma pr_after_push_unit:
      ∀f2,f. ⫯f2 ⊚ 𝐮❨𝟏❩ ≘ f → 𝐮❨𝟏❩ ⊚ f2 ≘ f.
#f2 #f #H
@(pr_after_pat_uni … (⫯f2))
/2 width=3 by pr_pat_refl/
qed.

(*** after_uni_one_sn *)
lemma pr_after_unit_sn:
      ∀f1,f. 𝐮❨𝟏❩ ⊚ f1 ≘ f → ⫯f1 ⊚ 𝐮❨𝟏❩ ≘ f.
/3 width=3 by pr_pat_after_uni_tls, pr_pat_refl/ qed-.
