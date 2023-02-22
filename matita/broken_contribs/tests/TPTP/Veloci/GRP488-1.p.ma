
include "logic/equality.ma".
(* Inclusion of: GRP488-1.p *)
(* -------------------------------------------------------------------------- *)
(*  File     : GRP488-1 : TPTP v3.1.1. Released v2.6.0. *)
(*  Domain   : Group Theory *)
(*  Problem  : Axiom for group theory, in double division and identity, part 2 *)
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
(*             Number of functors    :    5 (   2 constant; 0-2 arity) *)
(*             Number of variables   :    7 (   0 singleton) *)
(*             Maximal term depth    :    7 (   2 average) *)
(*  Comments : A UEQ part of GRP077-1 *)
(* -------------------------------------------------------------------------- *)
theorem prove_these_axioms_2:
 \forall Univ:Set.
\forall a2:Univ.
\forall double_divide:\forall _:Univ.\forall _:Univ.Univ.
\forall identity:Univ.
\forall inverse:\forall _:Univ.Univ.
\forall multiply:\forall _:Univ.\forall _:Univ.Univ.
\forall H0:\forall A:Univ.eq Univ identity (double_divide A (inverse A)).
\forall H1:\forall A:Univ.eq Univ (inverse A) (double_divide A identity).
\forall H2:\forall A:Univ.\forall B:Univ.eq Univ (multiply A B) (double_divide (double_divide B A) identity).
\forall H3:\forall A:Univ.\forall B:Univ.\forall C:Univ.eq Univ (double_divide A (double_divide (double_divide (double_divide identity (double_divide (double_divide A identity) (double_divide B C))) B) identity)) C.eq Univ (multiply identity a2) a2
.
intros.
autobatch paramodulation timeout=100;
try assumption.
print proofterm.
qed.
(* -------------------------------------------------------------------------- *)
