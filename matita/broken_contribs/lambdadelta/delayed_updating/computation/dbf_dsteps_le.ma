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

include "delayed_updating/reduction/dbf_dstep_le.ma".
include "delayed_updating/computation/dbf_dsteps.ma".

(* DELAYED BALANCED FOCUSED COMPUTATION IN A DEVELOPMENT ********************)

(* Constructions with subset_le *********************************************)

lemma dbfdss_subset_le_sx_conf (t1) (t2) (u1) (u2):
      t1 Ꟈ➡*𝐝𝐛𝐟[u1,u2] t2 → ∀v1. u1 ⊆ v1 →
      ∃∃v2. t1 Ꟈ➡*𝐝𝐛𝐟[v1,v2] t2 & u2 ⊆ v2.
#t1 #t2 #u1 #u2 #H12 elim H12 -t1 -t2 -u1 -u2
[ #t1 #t2 #u1 #u2 #Ht12 #Hu12 #v1 #Huv1
  @(ex2_intro … v1)
  [ /2 width=1 by dbfdss_refl/
  | @(subset_le_eq_repl … Huv1) -Huv1 //
  ]
| #t1 #t2 #u1 #u2 #H12 #v1 #Huv1
  elim (dbfds_subset_le_sx_conf … H12 Huv1) -u1 #v2 #H12 #Huv2
  /3 width=3 by dbfdss_step, ex2_intro/
| #t0 #t1 #t2 #u0 #u1 #u2 #_ #_ #IH1 #IH2 #v1 #Huv1
  elim (IH1 … Huv1) -u1 #v0 #H10 #Huv0
  elim (IH2 … Huv0) -u0 #v2 #H02 #Huv2
  /3 width=4 by dbfdss_trans, ex2_intro/
]
qed-.
