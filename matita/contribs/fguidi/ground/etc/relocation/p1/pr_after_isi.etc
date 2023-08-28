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

include "ground/relocation/p1/pr_isi.ma".
include "ground/relocation/p1/pr_after_after.ma".

(* RELATIONAL COMPOSITION FOR PARTIAL RELOCATION MAPS ***********************)

(* Constructions with pr_isi ************************************************)

(*** after_isid_sn *)
corec lemma pr_after_isi_sn:
            ∀f1. 𝐈❨f1❩ → ∀f2. f1 ⊚ f2 ≘ f2.
#f1 * -f1
#f1 #g1 #Hf1 #H1 #f2 cases (pr_map_split_tl f2) #H2
/3 width=7 by pr_after_push, pr_after_refl/
qed.

(*** after_isid_dx *)
corec lemma pr_after_isi_dx:
            ∀f2. 𝐈❨f2❩ → ∀f1. f1 ⊚ f2 ≘ f1.
#f2 * -f2
#f2 #g2 #Hf2 #H2 #f1 cases (pr_map_split_tl f1) #H1
[ /3 width=7 by pr_after_refl/
| @(pr_after_next … H1 H1) /3 width=3 by pr_isi_push/
]
qed.

(* Destructions with pr_isi *************************************************)

(*** after_isid_inv_sn *)
lemma pr_after_isi_inv_sn:
      ∀f1,f2,f. f1 ⊚ f2 ≘ f → 𝐈❨f1❩ → f2 ≐ f.
/3 width=6 by pr_after_isi_sn, pr_after_mono/ qed-.

(*** after_isid_inv_dx *)
lemma pr_after_isi_inv_dx:
      ∀f1,f2,f. f1 ⊚ f2 ≘ f → 𝐈❨f2❩ → f1 ≐ f.
/3 width=6 by pr_after_isi_dx, pr_after_mono/ qed-.

(*** after_fwd_isid1 *)
corec lemma pr_after_des_isi_sn:
            ∀f1,f2,f. f1 ⊚ f2 ≘ f → 𝐈❨f❩ → 𝐈❨f1❩.
#f1 #f2 #f * -f1 -f2 -f
#f1 #f2 #f #g1 [1,2: #g2 ] #g #Hf #H1 [1,2: #H2 ] #H0 #H
[ /4 width=6 by pr_isi_inv_push, pr_isi_push/ ]
cases (pr_isi_inv_next … H … H0)
qed-.

(*** after_fwd_isid2 *)
corec lemma pr_after_des_isi_dx:
            ∀f1,f2,f. f1 ⊚ f2 ≘ f → 𝐈❨f❩ → 𝐈❨f2❩.
#f1 #f2 #f * -f1 -f2 -f
#f1 #f2 #f #g1 [1,2: #g2 ] #g #Hf #H1 [1,2: #H2 ] #H0 #H
[ /4 width=6 by pr_isi_inv_push, pr_isi_push/ ]
cases (pr_isi_inv_next … H … H0)
qed-.

(*** after_inv_isid3 *)
lemma pr_after_inv_isi:
      ∀f1,f2,f. f1 ⊚ f2 ≘ f → 𝐈❨f❩ → 𝐈❨f1❩ ∧ 𝐈❨f2❩.
/3 width=4 by pr_after_des_isi_dx, pr_after_des_isi_sn, conj/ qed-.
