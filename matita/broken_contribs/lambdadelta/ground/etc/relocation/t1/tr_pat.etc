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

include "ground/arith/pnat_le_plus.ma".
include "ground/relocation/p1/pr_pat_lt.ma".
include "ground/relocation/t1/tr_map.ma".

(* TOTAL RELOCATION MAPS ****************************************************)

(* Constructions with pr_pat ************************************************)

(*** at_O1 *)
lemma tr_pat_unit_sn: ∀i2,f. ＠⧣❨𝟏,𝐭❨i2⨮f❩❩ ≘ i2.
#i2 elim i2 -i2 /2 width=5 by pr_pat_refl, pr_pat_next/
qed.

(*** at_S1 *)
lemma tr_pat_succ_sn: ∀p,f,i1,i2. ＠⧣❨i1, 𝐭❨f❩❩ ≘ i2 → ＠⧣❨↑i1, 𝐭❨p⨮f❩❩ ≘ i2+p.
#p elim p -p /3 width=7 by pr_pat_push, pr_pat_next/
qed.

(*** at_plus2 *)
lemma tr_pat_plus_dx (f):
      ∀i1,i,p,q. ＠⧣❨i1, 𝐭❨p⨮f❩❩ ≘ i → ＠⧣❨i1, 𝐭❨(p+q)⨮f❩❩ ≘ i+q.
#f #i1 #i #p #q #H elim q -q
/2 width=5 by pr_pat_next/
qed.

(* Inversions with pr_pat ***************************************************)

(*** at_inv_O1 *)
lemma tr_pat_inv_unit_sn (f):
      ∀p,i2. ＠⧣❨𝟏, 𝐭❨p⨮f❩❩ ≘ i2 → p = i2.
#f #p elim p -p /2 width=6 by pr_pat_inv_unit_push/
#p #IH #i2 #H elim (pr_pat_inv_next … H) -H [|*: // ]
#j2 #Hj * -i2 /3 width=1 by eq_f/
qed-.

(*** at_inv_S1 *)
lemma tr_pat_inv_succ_sn (f):
      ∀p,j1,i2. ＠⧣❨↑j1, 𝐭❨p⨮f❩❩ ≘ i2 →
      ∃∃j2. ＠⧣❨j1, 𝐭❨f❩❩ ≘ j2 & j2+p = i2.
#f #p elim p -p /2 width=5 by pr_pat_inv_succ_push/
#p #IH #j1 #i2 #H elim (pr_pat_inv_next … H) -H [|*: // ]
#j2 #Hj * -i2 elim (IH … Hj) -IH -Hj
#i2 #Hi * -j2 /2 width=3 by ex2_intro/
qed-.

(* Destructions with pr_pat *************************************************)

(* Note: a better conclusion would be: "i1 + ↓p ≤ i2" *)
(*** at_increasing_plus *)
lemma tr_pat_increasing_plus (f):
      ∀p,i1,i2. ＠⧣❨i1, 𝐭❨p⨮f❩❩ ≘ i2 → i1 + p ≤ ↑i2.
#f #p *
[ #i2 #H <(tr_pat_inv_unit_sn … H) -i2 //
| #i1 #i2 #H elim (tr_pat_inv_succ_sn … H) -H
  #j1 #Ht * -i2 <pplus_succ_sn 
  /4 width=2 by pr_pat_increasing, ple_plus_bi_dx, ple_succ_bi/
]
qed-.

(*** at_fwd_id *)
lemma tr_pat_des_id (f):
      ∀p,i. ＠⧣❨i, 𝐭❨p⨮f❩❩ ≘ i → 𝟏 = p.
#f #p #i #H lapply (pr_pat_des_id … H) -H #H
elim (eq_inv_pr_push_cons … H) -H //
qed-.
