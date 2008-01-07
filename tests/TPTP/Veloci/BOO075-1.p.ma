
include "logic/equality.ma".
(* Inclusion of: BOO075-1.p *)
(* -------------------------------------------------------------------------- *)
(*  File     : BOO075-1 : TPTP v3.1.1. Released v2.6.0. *)
(*  Domain   : Boolean Algebra *)
(*  Problem  : Sh-1 is a single axiom for Boolean algebra, part 1 *)
(*  Version  : [EF+02] axioms. *)
(*  English  :  *)
(*  Refs     : [EF+02] Ernst et al. (2002), More First-order Test Problems in *)
(*           : [MV+02] McCune et al. (2002), Short Single Axioms for Boolean *)
(*  Source   : [TPTP] *)
(*  Names    :  *)
(*  Status   : Unsatisfiable *)
(*  Rating   : 0.00 v2.6.0 *)
(*  Syntax   : Number of clauses     :    2 (   0 non-Horn;   2 unit;   1 RR) *)
(*             Number of atoms       :    2 (   2 equality) *)
(*             Maximal clause size   :    1 (   1 average) *)
(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors    :    3 (   2 constant; 0-2 arity) *)
(*             Number of variables   :    3 (   1 singleton) *)
(*             Maximal term depth    :    5 (   2 average) *)
(*  Comments : A UEQ part of BOO039-1 *)
(* -------------------------------------------------------------------------- *)
theorem prove_meredith_2_basis_1:
 \forall Univ:Set.
\forall a:Univ.
\forall b:Univ.
\forall nand:\forall _:Univ.\forall _:Univ.Univ.
\forall H0:\forall A:Univ.\forall B:Univ.\forall C:Univ.eq Univ (nand (nand A (nand (nand B A) A)) (nand B (nand C A))) B.eq Univ (nand (nand a a) (nand b a)) a
.
intros.
autobatch paramodulation timeout=100;
try assumption.
print proofterm.
qed.
(* -------------------------------------------------------------------------- *)
