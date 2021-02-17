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

include "ground/notation/relations/ringeq_3.ma".
include "ground/lib/stream.ma".

(* EXTENSIONAL EQUIVALENCE FOR STREAMS **************************************)

coinductive stream_eq (A): relation (stream A) ≝
| stream_eq_cons: ∀t1,t2,b1,b2. b1 = b2 → stream_eq A t1 t2 → stream_eq A (b1⨮t1) (b2⨮t2)
.

interpretation
  "extensional equivalence (streams)"
  'RingEq A t1 t2 = (stream_eq A t1 t2).

definition stream_eq_repl (A) (R:relation …) ≝
           ∀t1,t2. t1 ≗{A} t2 → R t1 t2.

definition stream_eq_repl_back (A) (R:predicate …) ≝
           ∀t1. R t1 → ∀t2. t1 ≗{A} t2 → R t2.

definition stream_eq_repl_fwd (A) (R:predicate …) ≝
           ∀t1. R t1 → ∀t2. t2 ≗{A} t1 → R t2.

(* Basic inversions *********************************************************)

lemma stream_eq_inv_cons: ∀A,t1,t2. t1 ≗{A} t2 →
                          ∀u1,u2,a1,a2. a1⨮u1 = t1 → a2⨮u2 = t2 →
                          u1 ≗ u2 ∧ a1 = a2.
#A #t1 #t2 * -t1 -t2
#t1 #t2 #b1 #b2 #Hb #Ht #u1 #u2 #a1 #a2 #H1 #H2 destruct /2 width=1 by conj/
qed-.

(* Basic constructions ******************************************************)

corec lemma stream_eq_refl: ∀A. reflexive … (stream_eq A).
#A * #b #t @stream_eq_cons //
qed.

corec lemma stream_eq_sym: ∀A. symmetric … (stream_eq A).
#A #t1 #t2 * -t1 -t2
#t1 #t2 #b1 #b2 #Hb #Ht @stream_eq_cons /2 width=1 by/
qed-.

lemma stream_eq_repl_sym: ∀A,R. stream_eq_repl_back A R → stream_eq_repl_fwd A R.
/3 width=3 by stream_eq_sym/ qed-.

(* Main constructions *******************************************************)

corec theorem stream_eq_trans: ∀A. Transitive … (stream_eq A).
#A #t1 #t * -t1 -t
#t1 #t #b1 #b * #Ht1 * #b2 #t2 #H cases (stream_eq_inv_cons A … H) -H -b
/3 width=7 by stream_eq_cons/
qed-.

theorem stream_eq_canc_sn: ∀A,t,t1,t2. t ≗ t1 → t ≗ t2 → t1 ≗{A} t2.
/3 width=3 by stream_eq_trans, stream_eq_sym/ qed-.

theorem stream_eq_canc_dx: ∀A,t,t1,t2. t1 ≗ t → t2 ≗ t → t1 ≗{A} t2.
/3 width=3 by stream_eq_trans, stream_eq_sym/ qed-.
