
include "logic/equality.ma".
(* Inclusion of: GRP595-1.p *)
(* -------------------------------------------------------------------------- *)
(*  File     : GRP595-1 : TPTP v3.1.1. Released v2.6.0. *)
(*  Domain   : Group Theory (Abelian) *)
(*  Problem  : Axiom for Abelian group theory, in double div and inv, part 3 *)
(*  Version  : [McC93] (equality) axioms. *)
(*  English  :  *)
(*  Refs     : [McC93] McCune (1993), Single Axioms for Groups and Abelian Gr *)
(*  Source   : [TPTP] *)
(*  Names    :  *)
(*  Status   : Unsatisfiable *)
(*  Rating   : 0.07 v3.1.0, 0.11 v2.7.0, 0.00 v2.6.0 *)
(*  Syntax   : Number of clauses     :    3 (   0 non-Horn;   3 unit;   1 RR) *)
(*             Number of atoms       :    3 (   3 equality) *)
(*             Maximal clause size   :    1 (   1 average) *)
(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors    :    6 (   3 constant; 0-2 arity) *)
(*             Number of variables   :    5 (   0 singleton) *)
(*             Maximal term depth    :    7 (   3 average) *)
(*  Comments : A UEQ part of GRP106-1 *)
(* -------------------------------------------------------------------------- *)
theorem prove_these_axioms_3:
 \forall Univ:Set.
\forall a3:Univ.
\forall b3:Univ.
\forall c3:Univ.
\forall double_divide:\forall _:Univ.\forall _:Univ.Univ.
\forall inverse:\forall _:Univ.Univ.
\forall multiply:\forall _:Univ.\forall _:Univ.Univ.
\forall H0:\forall A:Univ.\forall B:Univ.eq Univ (multiply A B) (inverse (double_divide B A)).
\forall H1:\forall A:Univ.\forall B:Univ.\forall C:Univ.eq Univ (inverse (double_divide (double_divide A B) (inverse (double_divide A (inverse (double_divide C B)))))) C.eq Univ (multiply (multiply a3 b3) c3) (multiply a3 (multiply b3 c3))
.
intros.
autobatch paramodulation timeout=100;
try assumption.
print proofterm.
qed.
(* -------------------------------------------------------------------------- *)
