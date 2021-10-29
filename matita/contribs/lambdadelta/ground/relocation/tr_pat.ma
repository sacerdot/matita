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

include "ground/notation/functions/apply_2.ma".
include "ground/arith/pnat_plus.ma".
include "ground/relocation/pr_pat.ma".
include "ground/relocation/tr_map.ma".
(*
include "ground/arith/pnat_le_plus.ma".
include "ground/relocation/pstream_eq.ma".
include "ground/relocation/rtmap_istot.ma".
*)
(* POSITIVE APPLICATION FOR TOTAL RELOCATION MAPS ***************************)

(*** apply *)
rec definition tr_pat (i: pnat) on i: tr_map → pnat.
* #p #f cases i -i
[ @p
| #i lapply (tr_pat i f) -tr_pat -i -f
  #i @(i+p)
]
defined.

interpretation
  "functional positive application (total relocation maps)"
  'apply f i = (tr_pat i f).

(* Constructions with pr_pat ***********************************************)

(*** at_O1 *)
lemma pr_pat_unit_sn: ∀i2,f. @❨𝟏,𝐭❨i2⨮f❩❩ ≘ i2.
#i2 elim i2 -i2 /2 width=5 by gr_pat_refl, gr_pat_next/
qed.

lemma at_S1: ∀p,f,i1,i2. @❨i1, f❩ ≘ i2 → @❨↑i1, p⨮f❩ ≘ i2+p.
#p elim p -p /3 width=7 by gr_pat_push, gr_pat_next/
qed.

lemma at_total: ∀i1,f. @❨i1, f❩ ≘ f@❨i1❩.
#i1 elim i1 -i1
[ * // | #i #IH * /3 width=1 by at_S1/ ]
qed.

lemma at_istot: ∀f. 𝐓❨f❩.
/2 width=2 by ex_intro/ qed.

lemma at_plus2: ∀f,i1,i,p,q. @❨i1, p⨮f❩ ≘ i → @❨i1, (p+q)⨮f❩ ≘ i+q.
#f #i1 #i #p #q #H elim q -q
/2 width=5 by gr_pat_next/
qed.

(* Inversion lemmas on at (specific) ******************************************)

lemma at_inv_O1: ∀f,p,i2. @❨𝟏, p⨮f❩ ≘ i2 → p = i2.
#f #p elim p -p /2 width=6 by gr_pat_inv_unit_push/
#p #IH #i2 #H elim (gr_pat_inv_next … H) -H [|*: // ]
#j2 #Hj * -i2 /3 width=1 by eq_f/
qed-.

lemma at_inv_S1: ∀f,p,j1,i2. @❨↑j1, p⨮f❩ ≘ i2 →
                 ∃∃j2. @❨j1, f❩ ≘ j2 & j2+p = i2.
#f #p elim p -p /2 width=5 by gr_pat_inv_succ_push/
#p #IH #j1 #i2 #H elim (gr_pat_inv_next … H) -H [|*: // ]
#j2 #Hj * -i2 elim (IH … Hj) -IH -Hj
#i2 #Hi * -j2 /2 width=3 by ex2_intro/
qed-.

lemma at_inv_total: ∀f,i1,i2. @❨i1, f❩ ≘ i2 → f@❨i1❩ = i2.
/2 width=6 by fr2_nat_mono/ qed-.

(* Forward lemmas on at (specific) *******************************************)

lemma at_increasing_plus: ∀f,p,i1,i2. @❨i1, p⨮f❩ ≘ i2 → i1 + p ≤ ↑i2.
#f #p *
[ #i2 #H <(at_inv_O1 … H) -i2 //
| #i1 #i2 #H elim (at_inv_S1 … H) -H
  #j1 #Ht * -i2 <pplus_succ_sn 
  /4 width=2 by gr_pat_increasing, ple_plus_bi_dx, ple_succ_bi/
]
qed-.

lemma at_fwd_id: ∀f,p,i. @❨i, p⨮f❩ ≘ i → 𝟏 = p.
#f #p #i #H elim (gr_pat_des_id … H) -H
#g #H elim (push_inv_seq_dx … H) -H //
qed-.

(* Basic properties *********************************************************)

lemma tr_pat_O1: ∀p,f. (p⨮f)@❨𝟏❩ = p.
// qed.

lemma tr_pat_S1: ∀p,f,i. (p⨮f)@❨↑i❩ = f@❨i❩+p.
// qed.

lemma tr_pat_eq_repl (i): gr_eq_repl … (λf1,f2. f1@❨i❩ = f2@❨i❩).
#i elim i -i [2: #i #IH ] * #p1 #f1 * #p2 #f2 #H
elim (eq_inv_seq_aux … H) -H #Hp #Hf //
>tr_pat_S1 >tr_pat_S1 /3 width=1 by eq_f2/
qed.

lemma tr_pat_S2: ∀f,i. (↑f)@❨i❩ = ↑(f@❨i❩).
* #p #f * //
qed.

(* Main inversion lemmas ****************************************************)

theorem tr_pat_inj: ∀f,i1,i2,j. f@❨i1❩ = j → f@❨i2❩ = j → i1 = i2.
/2 width=4 by gr_pat_inj/ qed-.

corec theorem nstream_eq_inv_ext: ∀f1,f2. (∀i. f1@❨i❩ = f2@❨i❩) → f1 ≗ f2.
* #p1 #f1 * #p2 #f2 #Hf @stream_eq_cons
[ @(Hf (𝟏))
| @nstream_eq_inv_ext -nstream_eq_inv_ext #i
  ltr_pat (Hf (𝟏)) >tr_pat_O1 >tr_pat_O1 #H destruct
  ltr_pat (Hf (↑i)) >tr_pat_S1 >tr_pat_S1 #H
  /3 width=2 by eq_inv_pplus_bi_dx, eq_inv_psucc_bi/
]
qed-.
