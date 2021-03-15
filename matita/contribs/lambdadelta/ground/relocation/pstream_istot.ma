(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.tcs.unibo.it                            *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "ground/notation/functions/apply_2.ma".
include "ground/arith/pnat_le_plus.ma".
include "ground/relocation/pstream_eq.ma".
include "ground/relocation/rtmap_istot.ma".

(* RELOCATION N-STREAM ******************************************************)

rec definition apply (i: pnat) on i: rtmap → pnat.
* #p #f cases i -i
[ @p
| #i lapply (apply i f) -apply -i -f
  #i @(i+p)
]
defined.

interpretation "functional application (nstream)"
   'Apply f i = (apply i f).

(* Specific properties on at ************************************************)

lemma at_O1: ∀i2,f. @❪𝟏, i2⨮f❫ ≘ i2.
#i2 elim i2 -i2 /2 width=5 by at_refl, at_next/
qed.

lemma at_S1: ∀p,f,i1,i2. @❪i1, f❫ ≘ i2 → @❪↑i1, p⨮f❫ ≘ i2+p.
#p elim p -p /3 width=7 by at_push, at_next/
qed.

lemma at_total: ∀i1,f. @❪i1, f❫ ≘ f@❨i1❩.
#i1 elim i1 -i1
[ * // | #i #IH * /3 width=1 by at_S1/ ]
qed.

lemma at_istot: ∀f. 𝐓❪f❫.
/2 width=2 by ex_intro/ qed.

lemma at_plus2: ∀f,i1,i,p,q. @❪i1, p⨮f❫ ≘ i → @❪i1, (p+q)⨮f❫ ≘ i+q.
#f #i1 #i #p #q #H elim q -q
/2 width=5 by at_next/
qed.

(* Specific inversion lemmas on at ******************************************)

lemma at_inv_O1: ∀f,p,i2. @❪𝟏, p⨮f❫ ≘ i2 → p = i2.
#f #p elim p -p /2 width=6 by at_inv_ppx/
#p #IH #i2 #H elim (at_inv_xnx … H) -H [|*: // ]
#j2 #Hj * -i2 /3 width=1 by eq_f/
qed-.

lemma at_inv_S1: ∀f,p,j1,i2. @❪↑j1, p⨮f❫ ≘ i2 →
                 ∃∃j2. @❪j1, f❫ ≘ j2 & j2+p = i2.
#f #p elim p -p /2 width=5 by at_inv_npx/
#p #IH #j1 #i2 #H elim (at_inv_xnx … H) -H [|*: // ]
#j2 #Hj * -i2 elim (IH … Hj) -IH -Hj
#i2 #Hi * -j2 /2 width=3 by ex2_intro/
qed-.

lemma at_inv_total: ∀f,i1,i2. @❪i1, f❫ ≘ i2 → f@❨i1❩ = i2.
/2 width=6 by at_mono/ qed-.

(* Spercific forward lemmas on at *******************************************)

lemma at_increasing_plus: ∀f,p,i1,i2. @❪i1, p⨮f❫ ≘ i2 → i1 + p ≤ ↑i2.
#f #p *
[ #i2 #H <(at_inv_O1 … H) -i2 //
| #i1 #i2 #H elim (at_inv_S1 … H) -H
  #j1 #Ht * -i2 <pplus_succ_sn 
  /4 width=2 by at_increasing, ple_plus_bi_dx, ple_succ_bi/
]
qed-.

lemma at_fwd_id: ∀f,p,i. @❪i, p⨮f❫ ≘ i → 𝟏 = p.
#f #p #i #H elim (at_fwd_id_ex … H) -H
#g #H elim (push_inv_seq_dx … H) -H //
qed-.

(* Basic properties *********************************************************)

lemma apply_O1: ∀p,f. (p⨮f)@❨𝟏❩ = p.
// qed.

lemma apply_S1: ∀p,f,i. (p⨮f)@❨↑i❩ = f@❨i❩+p.
// qed.

lemma apply_eq_repl (i): eq_repl … (λf1,f2. f1@❨i❩ = f2@❨i❩).
#i elim i -i [2: #i #IH ] * #p1 #f1 * #p2 #f2 #H
elim (eq_inv_seq_aux … H) -H #Hp #Hf //
>apply_S1 >apply_S1 /3 width=1 by eq_f2/
qed.

lemma apply_S2: ∀f,i. (↑f)@❨i❩ = ↑(f@❨i❩).
* #p #f * //
qed.

(* Main inversion lemmas ****************************************************)

theorem apply_inj: ∀f,i1,i2,j. f@❨i1❩ = j → f@❨i2❩ = j → i1 = i2.
/2 width=4 by at_inj/ qed-.

corec theorem nstream_eq_inv_ext: ∀f1,f2. (∀i. f1@❨i❩ = f2@❨i❩) → f1 ≗ f2.
* #p1 #f1 * #p2 #f2 #Hf @stream_eq_cons
[ @(Hf (𝟏))
| @nstream_eq_inv_ext -nstream_eq_inv_ext #i
  lapply (Hf (𝟏)) >apply_O1 >apply_O1 #H destruct
  lapply (Hf (↑i)) >apply_S1 >apply_S1 #H
  /3 width=2 by eq_inv_pplus_bi_dx, eq_inv_psucc_bi/
]
qed-.
