
include "logic/equality.ma".
(* Inclusion of: GRP459-1.p *)
(* -------------------------------------------------------------------------- *)
(*  File     : GRP459-1 : TPTP v3.1.1. Released v2.6.0. *)
(*  Domain   : Group Theory *)
(*  Problem  : Axiom for group theory, in division and identity, part 3 *)
(*  Version  : [McC93] (equality) axioms. *)
(*  English  :  *)
(*  Refs     : [McC93] McCune (1993), Single Axioms for Groups and Abelian Gr *)
(*  Source   : [TPTP] *)
(*  Names    :  *)
(*  Status   : Unsatisfiable *)
(*  Rating   : 0.00 v2.6.0 *)
(*  Syntax   : Number of clauses     :    5 (   0 non-Horn;   5 unit;   1 RR) *)
(*             Number of atoms       :    5 (   5 equality) *)
(*             Maximal clause size   :    1 (   1 average) *)
(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors    :    7 (   4 constant; 0-2 arity) *)
(*             Number of variables   :    7 (   0 singleton) *)
(*             Maximal term depth    :    7 (   3 average) *)
(*  Comments : A UEQ part of GRP067-1 *)
(* -------------------------------------------------------------------------- *)
theorem prove_these_axioms_3:
 \forall Univ:Set.
\forall a3:Univ.
\forall b3:Univ.
\forall c3:Univ.
\forall divide:\forall _:Univ.\forall _:Univ.Univ.
\forall identity:Univ.
\forall inverse:\forall _:Univ.Univ.
\forall multiply:\forall _:Univ.\forall _:Univ.Univ.
\forall H0:\forall A:Univ.eq Univ identity (divide A A).
\forall H1:\forall A:Univ.eq Univ (inverse A) (divide identity A).
\forall H2:\forall A:Univ.\forall B:Univ.eq Univ (multiply A B) (divide A (divide identity B)).
\forall H3:\forall A:Univ.\forall B:Univ.\forall C:Univ.eq Univ (divide (divide (divide A A) (divide A (divide B (divide (divide identity A) C)))) C) B.eq Univ (multiply (multiply a3 b3) c3) (multiply a3 (multiply b3 c3))
.
intros.
autobatch paramodulation timeout=100;
try assumption.
print proofterm.
qed.
(* -------------------------------------------------------------------------- *)
