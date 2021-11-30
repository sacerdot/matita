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
include "ground/relocation/tr_pat.ma".

(* POSITIVE APPLICATION FOR TOTAL RELOCATION MAPS ***************************)

(*** apply *)
rec definition tr_pap (i: pnat) on i: tr_map → pnat.
* #p #f cases i -i
[ @p
| #i lapply (tr_pap i f) -tr_pap -i -f
  #i @(i+p)
]
defined.

interpretation
  "functional positive application (total relocation maps)"
  'Apply f i = (tr_pap i f).

(* Constructions with pr_pat ***********************************************)

(*** at_total *)
lemma tr_pat_total: ∀i1,f. @❨i1,𝐭❨f❩❩ ≘ f@❨i1❩.
#i1 elim i1 -i1
[ * // | #i #IH * /3 width=1 by pr_pat_succ_sn/ ]
qed.

(* Inversions with pr_pat ***************************************************)

lemma at_inv_total: ∀f,i1,i2. @❨i1, f❩ ≘ i2 → f@❨i1❩ = i2.
/2 width=6 by fr2_nat_mono/ qed-.

(* Basic properties *********************************************************)

lemma apply_O1: ∀p,f. (p⨮f)@❨𝟏❩ = p.
// qed.

lemma apply_S1: ∀p,f,i. (p⨮f)@❨↑i❩ = f@❨i❩+p.
// qed.

lemma apply_eq_repl (i): gr_eq_repl … (λf1,f2. f1@❨i❩ = f2@❨i❩).
#i elim i -i [2: #i #IH ] * #p1 #f1 * #p2 #f2 #H
elim (eq_inv_seq_aux … H) -H #Hp #Hf //
>apply_S1 >apply_S1 /3 width=1 by eq_f2/
qed.

lemma apply_S2: ∀f,i. (↑f)@❨i❩ = ↑(f@❨i❩).
* #p #f * //
qed.

(* Main inversion lemmas ****************************************************)

theorem apply_inj: ∀f,i1,i2,j. f@❨i1❩ = j → f@❨i2❩ = j → i1 = i2.
/2 width=4 by gr_pat_inj/ qed-.

corec theorem nstream_eq_inv_ext: ∀f1,f2. (∀i. f1@❨i❩ = f2@❨i❩) → f1 ≗ f2.
* #p1 #f1 * #p2 #f2 #Hf @stream_eq_cons
[ @(Hf (𝟏))
| @nstream_eq_inv_ext -nstream_eq_inv_ext #i
  lapply (Hf (𝟏)) >apply_O1 >apply_O1 #H destruct
  lapply (Hf (↑i)) >apply_S1 >apply_S1 #H
  /3 width=2 by eq_inv_pplus_bi_dx, eq_inv_psucc_bi/
]
qed-.

(*
include "ground/relocation/pstream_eq.ma".
*)

(*
include "ground/relocation/rtmap_istot.ma".

lemma at_istot: ∀f. 𝐓❨f❩.
/2 width=2 by ex_intro/ qed.
*)
