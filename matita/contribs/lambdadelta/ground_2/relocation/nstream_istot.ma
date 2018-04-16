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

include "ground_2/notation/functions/apply_2.ma".
include "ground_2/relocation/nstream_eq.ma".
include "ground_2/relocation/rtmap_istot.ma".

(* RELOCATION N-STREAM ******************************************************)

rec definition apply (i: nat) on i: rtmap → nat ≝ ?.
* #n #f cases i -i
[ @n
| #i lapply (apply i f) -apply -i -f
  #i @(⫯(n+i))
]
defined.

interpretation "functional application (nstream)"
   'Apply f i = (apply i f).

(* Specific properties on at ************************************************)

lemma at_O1: ∀i2,f. @⦃0, i2@f⦄ ≘ i2.
#i2 elim i2 -i2 /2 width=5 by at_refl, at_next/
qed.

lemma at_S1: ∀n,f,i1,i2. @⦃i1, f⦄ ≘ i2 → @⦃⫯i1, n@f⦄ ≘ ⫯(n+i2).
#n elim n -n /3 width=7 by at_push, at_next/
qed.

lemma at_total: ∀i1,f. @⦃i1, f⦄ ≘ f@❴i1❵.
#i1 elim i1 -i1
[ * // | #i #IH * /3 width=1 by at_S1/ ]
qed.

lemma at_istot: ∀f. 𝐓⦃f⦄.
/2 width=2 by ex_intro/ qed.

lemma at_plus2: ∀f,i1,i,n,m. @⦃i1, n@f⦄ ≘ i → @⦃i1, (m+n)@f⦄ ≘ m+i.
#f #i1 #i #n #m #H elim m -m //
#m <plus_S1 /2 width=5 by at_next/ (**) (* full auto fails *)
qed.

(* Specific inversion lemmas on at ******************************************)

lemma at_inv_O1: ∀f,n,i2. @⦃0, n@f⦄ ≘ i2 → n = i2.
#f #n elim n -n /2 width=6 by at_inv_ppx/
#n #IH #i2 #H elim (at_inv_xnx … H) -H [2,3: // ]
#j2 #Hj * -i2 /3 width=1 by eq_f/
qed-.

lemma at_inv_S1: ∀f,n,j1,i2. @⦃⫯j1, n@f⦄ ≘ i2 →
                 ∃∃j2. @⦃j1, f⦄ ≘ j2 & ⫯(n+j2) = i2.
#f #n elim n -n /2 width=5 by at_inv_npx/
#n #IH #j1 #i2 #H elim (at_inv_xnx … H) -H [2,3: // ]
#j2 #Hj * -i2 elim (IH … Hj) -IH -Hj
#i2 #Hi * -j2 /2 width=3 by ex2_intro/
qed-.

lemma at_inv_total: ∀f,i1,i2. @⦃i1, f⦄ ≘ i2 → f@❴i1❵ = i2.
/2 width=6 by at_mono/ qed-.

(* Spercific forward lemmas on at *******************************************)

lemma at_increasing_plus: ∀f,n,i1,i2. @⦃i1, n@f⦄ ≘ i2 → i1 + n ≤ i2.
#f #n *
[ #i2 #H <(at_inv_O1 … H) -i2 //
| #i1 #i2 #H elim (at_inv_S1 … H) -H
  #j1 #Ht * -i2 /4 width=2 by at_increasing, monotonic_le_plus_r, le_S_S/
]
qed-.

lemma at_fwd_id: ∀f,n,i. @⦃i, n@f⦄ ≘ i → 0 = n.
#f #n #i #H elim (at_fwd_id_ex … H) -H
#g #H elim (push_inv_seq_dx … H) -H //
qed-.

(* Basic properties *********************************************************)

lemma apply_eq_repl (i): eq_repl … (λf1,f2. f1@❴i❵ = f2@❴i❵).
#i elim i -i [2: #i #IH ] * #n1 #f1 * #n2 #f2 #H
elim (eq_inv_seq_aux … H) -H normalize //
#Hn #Hf /4 width=1 by eq_f2, eq_f/
qed.

lemma apply_S1: ∀f,i. (⫯f)@❴i❵ = ⫯(f@❴i❵).
* #n #f * //
qed.

(* Main inversion lemmas ****************************************************)

theorem apply_inj: ∀f,i1,i2,j. f@❴i1❵ = j → f@❴i2❵ = j → i1 = i2.
/2 width=4 by at_inj/ qed-.
