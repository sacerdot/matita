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

include "ground_2/notation/constructors/cons_2.ma".
include "ground_2/notation/relations/exteq_3.ma".
include "ground_2/lib/star.ma".

(* STREAMS ******************************************************************)

coinductive stream (A:Type[0]): Type[0] ≝
| seq: A → stream A → stream A
.

interpretation "cons (nstream)" 'Cons b t = (seq ? b t).

coinductive eq_stream (A): relation (stream A) ≝
| eq_seq: ∀t1,t2,b1,b2. b1 = b2 → eq_stream A t1 t2 → eq_stream A (b1@t1) (b2@t2)
.

interpretation "extensional equivalence (nstream)"
   'ExtEq A t1 t2 = (eq_stream A t1 t2).

definition eq_stream_repl_back (A) (R:predicate …) ≝
                               ∀t1,t2. t1 ≐⦋A⦌ t2 → R t1 → R t2.

definition eq_stream_repl_fwd (A) (R:predicate …) ≝
                              ∀t1,t2. t2 ≐⦋A⦌ t1 → R t1 → R t2.

(* Basic inversion lemmas ***************************************************)

fact eq_stream_inv_seq_aux: ∀A,t1,t2. t1 ≐⦋A⦌ t2 →
                            ∀u1,u2,a1,a2. t1 = a1@u1 → t2 = a2@u2 →
                            a1 = a2 ∧ u1 ≐ u2.
#A #t1 #t2 * -t1 -t2
#t1 #t2 #b1 #b2 #Hb #Ht #u1 #u2 #a1 #a2 #H1 #H2 destruct /2 width=1 by conj/
qed-.

lemma eq_stream_inv_seq: ∀A,t1,t2,b1,b2. b1@t1 ≐⦋A⦌ b2@t2 → b1 = b2 ∧ t1 ≐ t2.
/2 width=5 by eq_stream_inv_seq_aux/ qed-.

(* Basic properties *********************************************************)

lemma stream_expand (A) (t:stream A): t = match t with [ seq a u ⇒ a @ u ].
#A * //
qed.

let corec eq_stream_refl: ∀A. reflexive … (eq_stream A) ≝ ?.
#A * #b #t @eq_seq //
qed.

let corec eq_stream_sym: ∀A. symmetric … (eq_stream A) ≝ ?.
#A #t1 #t2 * -t1 -t2
#t1 #t2 #b1 #b2 #Hb #Ht @eq_seq /2 width=1 by/
qed-.

lemma eq_stream_repl_sym: ∀A,R. eq_stream_repl_back A R → eq_stream_repl_fwd A R.
/3 width=3 by eq_stream_sym/ qed-.

(* Main properties **********************************************************)

let corec eq_stream_trans: ∀A. Transitive … (eq_stream A) ≝ ?.
#A #t1 #t * -t1 -t
#t1 #t #b1 #b #Hb1 #Ht1 * #b2 #t2 #H cases (eq_stream_inv_seq A … H) -H
#Hb2 #Ht2 @eq_seq /2 width=3 by/
qed-.

theorem eq_stream_canc_sn: ∀A,t,t1,t2. t ≐ t1 → t ≐ t2 → t1 ≐⦋A⦌ t2.
/3 width=3 by eq_stream_trans, eq_stream_sym/ qed-.

theorem eq_stream_canc_dx: ∀A,t,t1,t2. t1 ≐ t → t2 ≐ t → t1 ≐⦋A⦌ t2.
/3 width=3 by eq_stream_trans, eq_stream_sym/ qed-. 
