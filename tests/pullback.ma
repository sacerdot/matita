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

set "baseuri" "cic:/matita/tests/pullback".

inductive T : Type \def t : T.
inductive L : Type \def l : L.
inductive R : Type \def r : R.
inductive R1 : Type \def r1 : R1.
inductive P1 : Type \def p1 : P1.
inductive P2 : Type \def p2 : P2.

definition L_to_T : L \to T \def \lambda x.t.
definition R_to_T : R \to T \def \lambda x.t.
definition P1_to_L : P1 \to L \def \lambda x.l.
definition P1_to_R1 : P1 \to R1 \def \lambda x.r1.
definition R1_to_P2 : R1 \to P2 \def \lambda x.p2.
definition R1_to_R : R1 \to R \def \lambda x.r.
definition P2_to_L : P2 \to L \def \lambda x.l.
definition P2_to_R : P2 \to R \def \lambda x.r.
definition P1_to_P1 : P1 \to P1 \def \lambda x.p1.

coercion cic:/matita/tests/pullback/L_to_T.con.
coercion cic:/matita/tests/pullback/R_to_T.con.
coercion cic:/matita/tests/pullback/P1_to_L.con.
coercion cic:/matita/tests/pullback/P1_to_R1.con.
coercion cic:/matita/tests/pullback/R1_to_R.con.
coercion cic:/matita/tests/pullback/R1_to_P2.con.
coercion cic:/matita/tests/pullback/P2_to_L.con.
coercion cic:/matita/tests/pullback/P2_to_R.con.
coercion cic:/matita/tests/pullback/P1_to_P1.con.
