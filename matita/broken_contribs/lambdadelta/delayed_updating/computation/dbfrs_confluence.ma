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

include "ground/xoa/ex_2_3.ma".
include "delayed_updating/computation/dbfrs_preterm.ma".

(* DELAYED BALANCED FOCUSED COMPUTATION *************************************)

(* Confluence ***************************************************************)

axiom dbfrs_strip (t0):
      t0 ϵ 𝐓 → ∀t1,r1. t0 ➡𝐝𝐛𝐟[r1] t1 → ∀t2,rs2. t0 ➡*𝐝𝐛𝐟[rs2] t2 →
      ∃∃t,ss1,ss2. t1 ➡*𝐝𝐛𝐟[ss1] t & t2 ➡*𝐝𝐛𝐟[ss2] t.

lemma dbfrs_conf (t0):
      t0 ϵ 𝐓 → ∀t1,rs1. t0 ➡*𝐝𝐛𝐟[rs1] t1 → ∀t2,rs2. t0 ➡*𝐝𝐛𝐟[rs2] t2 →
      ∃∃t,ss1,ss2. t1 ➡*𝐝𝐛𝐟[ss1] t & t2 ➡*𝐝𝐛𝐟[ss2] t.
#t0 #Ht0 #t1 #rs1 #H0 @(dbfrs_ind_dx … H0) -t1 -rs1
[ #tx #t1 #rst1 #Htx1 #IH #t2 #rs2 #Ht02
  elim (IH … Ht02) -t0 #t #ss1 #ss2 #Ht1 #Ht2
  /3 width=5 by eq_dbfrs_trans, ex2_3_intro/
| #t2 #rs2 #Ht02
  /3 width=5 by frs_refl, ex2_3_intro/
| #tx #t1 #rs1 #s1 #Ht0x #Htx1 #IH #t2 #rs2 #Ht02
  lapply (dbfrs_preterm_trans … Ht0 Ht0x) -Ht0 -Ht0x #Hx
  elim (IH … Ht02) -t0 #t #ss1 #ss2 #Htx #Ht2
  elim (dbfrs_strip … Htx1 … Htx) // -tx #tx #xs1 #xs2 #ht1x #htx
  /3 width=8 by frs_trans, ex2_3_intro/
]
qed-.
