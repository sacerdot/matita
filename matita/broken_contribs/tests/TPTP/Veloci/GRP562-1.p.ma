
include "logic/equality.ma".
(* Inclusion of: GRP562-1.p *)
(* -------------------------------------------------------------------------- *)
(*  File     : GRP562-1 : TPTP v3.1.1. Released v2.6.0. *)
(*  Domain   : Group Theory (Abelian) *)
(*  Problem  : Axiom for Abelian group theory, in division and inverse, part 2 *)
(*  Version  : [McC93] (equality) axioms. *)
(*  English  :  *)
(*  Refs     : [McC93] McCune (1993), Single Axioms for Groups and Abelian Gr *)
(*  Source   : [TPTP] *)
(*  Names    :  *)
(*  Status   : Unsatisfiable *)
(*  Rating   : 0.00 v2.6.0 *)
(*  Syntax   : Number of clauses     :    3 (   0 non-Horn;   3 unit;   1 RR) *)
(*             Number of atoms       :    3 (   3 equality) *)
(*             Maximal clause size   :    1 (   1 average) *)
(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors    :    5 (   2 constant; 0-2 arity) *)
(*             Number of variables   :    5 (   0 singleton) *)
(*             Maximal term depth    :    5 (   3 average) *)
(*  Comments : A UEQ part of GRP098-1 *)
(* -------------------------------------------------------------------------- *)
theorem prove_these_axioms_2:
 \forall Univ:Set.
\forall a2:Univ.
\forall b2:Univ.
\forall divide:\forall _:Univ.\forall _:Univ.Univ.
\forall inverse:\forall _:Univ.Univ.
\forall multiply:\forall _:Univ.\forall _:Univ.Univ.
\forall H0:\forall A:Univ.\forall B:Univ.eq Univ (multiply A B) (divide A (inverse B)).
\forall H1:\forall A:Univ.\forall B:Univ.\forall C:Univ.eq Univ (divide (divide (divide A (inverse B)) C) (divide A C)) B.eq Univ (multiply (multiply (inverse b2) b2) a2) a2
.
intros.
autobatch paramodulation timeout=100;
try assumption.
print proofterm.
qed.
(* -------------------------------------------------------------------------- *)
