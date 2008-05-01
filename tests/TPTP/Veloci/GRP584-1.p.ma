
include "logic/equality.ma".
(* Inclusion of: GRP584-1.p *)
(* -------------------------------------------------------------------------- *)
(*  File     : GRP584-1 : TPTP v3.1.1. Bugfixed v2.7.0. *)
(*  Domain   : Group Theory (Abelian) *)
(*  Problem  : Axiom for Abelian group theory, in double div and id, part 4 *)
(*  Version  : [McC93] (equality) axioms. *)
(*  English  :  *)
(*  Refs     : [McC93] McCune (1993), Single Axioms for Groups and Abelian Gr *)
(*  Source   : [TPTP] *)
(*  Names    :  *)
(*  Status   : Unsatisfiable *)
(*  Rating   : 0.00 v2.7.0 *)
(*  Syntax   : Number of clauses     :    5 (   0 non-Horn;   5 unit;   1 RR) *)
(*             Number of atoms       :    5 (   5 equality) *)
(*             Maximal clause size   :    1 (   1 average) *)
(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors    :    6 (   3 constant; 0-2 arity) *)
(*             Number of variables   :    7 (   0 singleton) *)
(*             Maximal term depth    :    6 (   2 average) *)
(*  Comments : A UEQ part of GRP103-1 *)
(*  Bugfixes : v2.7.0 - Grounded conjecture *)
(* -------------------------------------------------------------------------- *)
theorem prove_these_axioms_4:
 \forall Univ:Set.
\forall a:Univ.
\forall b:Univ.
\forall double_divide:\forall _:Univ.\forall _:Univ.Univ.
\forall identity:Univ.
\forall inverse:\forall _:Univ.Univ.
\forall multiply:\forall _:Univ.\forall _:Univ.Univ.
\forall H0:\forall A:Univ.eq Univ identity (double_divide A (inverse A)).
\forall H1:\forall A:Univ.eq Univ (inverse A) (double_divide A identity).
\forall H2:\forall A:Univ.\forall B:Univ.eq Univ (multiply A B) (double_divide (double_divide B A) identity).
\forall H3:\forall A:Univ.\forall B:Univ.\forall C:Univ.eq Univ (double_divide (double_divide A (double_divide (double_divide identity B) (double_divide C (double_divide B A)))) (double_divide identity identity)) C.eq Univ (multiply a b) (multiply b a)
.
intros.
autobatch paramodulation timeout=100;
try assumption.
print proofterm.
qed.
(* -------------------------------------------------------------------------- *)
