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

(* BTM: MATITA SOURCE FILES
 * Suggested invocation to start formal specifications with:
 *   - Patience on me to gain peace and perfection! -
 * 2008 September 22:
 *   specification starts.
 *)

include "arith.ma".

(* CHARACTER CLASSES ********************************************************)

(* Note: OEIS sequence identifiers 
   P(n): A016777 "3n+1"
   T(n): A155504 "(3h+1)*3^(k+1)"
*)

inductive P: predicate nat ≝
   | p1: P 1
   | p2: ∀i,j. T i → P j → P (i + j)
with T: predicate nat ≝
   | t1: ∀i. P i → T (i * 3)
   | t2: ∀i. T i → T (i * 3)
.

inductive S: predicate nat ≝
   | s1: ∀i. P i → S (i * 2)
   | s2: ∀i. T i → S (i * 2)
.

inductive Q: predicate nat ≝
   | q1: ∀i. P i → Q (i * 2 + 3)
   | q2: ∀i. Q i → Q (i * 3)
.

(* Basic eliminators ********************************************************)

axiom p_ind: ∀R:predicate nat. R 1 →
             (∀i,j. T i → R j → R (i + j)) →
             ∀j. P j → R j.

axiom t_ind: ∀R:predicate nat.
             (∀i. P i → R (i * 3)) →
             (∀i. R i → R (i * 3)) →
             ∀i. T i → R i.

(* Basic inversion lemmas ***************************************************)

fact p_inv_O_aux: ∀i. P i → i = 0 → False.
#i #H @(p_ind … H) -i
[ #H destruct
| #i #j #_ #IH #H 
  elim (plus_inv_O3 … H) -H /2 width=1/
]
qed-.

lemma p_inv_O: P 0 → False.
/2 width=3 by p_inv_O_aux/ qed-.

fact t_inv_O_aux: ∀i. T i → i = 0 → False.
#i #H @(t_ind … H) -i #i #IH #H
lapply (times_inv_S2_O3 … H) -H /2 width=1/
/2 width=3 by p_inv_O_aux/
qed-.

lemma t_inv_O: T 0 → False.
/2 width=3 by t_inv_O_aux/ qed-.

(* Basic properties *********************************************************)

lemma t_3: T 3.
/2 width=1/ qed.

lemma p_pos: ∀i. P i → ∃k. i = k + 1.
* /2 width=2/
#H elim (p_inv_O … H) 
qed.

lemma t_pos: ∀i. T i → ∃k. i = k + 1.
* /2 width=2/
#H elim (t_inv_O … H) 
qed.
