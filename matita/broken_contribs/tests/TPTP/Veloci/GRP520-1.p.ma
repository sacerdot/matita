
include "logic/equality.ma".
(* Inclusion of: GRP520-1.p *)
(* -------------------------------------------------------------------------- *)
(*  File     : GRP520-1 : TPTP v3.1.1. Bugfixed v2.7.0. *)
(*  Domain   : Group Theory (Abelian) *)
(*  Problem  : Axiom for Abelian group theory, in product and inverse, part 4 *)
(*  Version  : [McC93] (equality) axioms. *)
(*  English  :  *)
(*  Refs     : [McC93] McCune (1993), Single Axioms for Groups and Abelian Gr *)
(*  Source   : [TPTP] *)
(*  Names    :  *)
(*  Status   : Unsatisfiable *)
(*  Rating   : 0.00 v2.7.0 *)
(*  Syntax   : Number of clauses     :    2 (   0 non-Horn;   2 unit;   1 RR) *)
(*             Number of atoms       :    2 (   2 equality) *)
(*             Maximal clause size   :    1 (   1 average) *)
(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors    :    4 (   2 constant; 0-2 arity) *)
(*             Number of variables   :    3 (   0 singleton) *)
(*             Maximal term depth    :    6 (   3 average) *)
(*  Comments : A UEQ part of GRP087-1 *)
(*  Bugfixes : v2.7.0 - Grounded conjecture *)
(* -------------------------------------------------------------------------- *)
theorem prove_these_axioms_4:
 \forall Univ:Set.
\forall a:Univ.
\forall b:Univ.
\forall inverse:\forall _:Univ.Univ.
\forall multiply:\forall _:Univ.\forall _:Univ.Univ.
\forall H0:\forall A:Univ.\forall B:Univ.\forall C:Univ.eq Univ (multiply A (multiply (multiply (inverse (multiply A B)) C) B)) C.eq Univ (multiply a b) (multiply b a)
.
intros.
autobatch paramodulation timeout=100;
try assumption.
print proofterm.
qed.
(* -------------------------------------------------------------------------- *)
