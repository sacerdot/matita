
include "logic/equality.ma".
(* Inclusion of: COL083-1.p *)
(* -------------------------------------------------------------------------- *)
(*  File     : COL083-1 : TPTP v3.1.1. Released v2.6.0. *)
(*  Domain   : Combinatory Logic *)
(*  Problem  : Compatible Birds, part 1 *)
(*  Version  : Especial. *)
(*  English  :  *)
(*  Refs     : [Smu85] Smullyan (1978), To Mock a Mocking Bird and Other Logi *)
(*  Source   : [TPTP] *)
(*  Names    :  *)
(*  Status   : Unsatisfiable *)
(*  Rating   : 0.00 v2.6.0 *)
(*  Syntax   : Number of clauses     :    3 (   0 non-Horn;   3 unit;   1 RR) *)
(*             Number of atoms       :    3 (   3 equality) *)
(*             Maximal clause size   :    1 (   1 average) *)
(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors    :    4 (   2 constant; 0-2 arity) *)
(*             Number of variables   :    6 (   2 singleton) *)
(*             Maximal term depth    :    3 (   2 average) *)
(*  Comments : A UEQ part of COL054-1 *)
(* -------------------------------------------------------------------------- *)
theorem prove_birds_are_compatible_1:
 \forall Univ:Set.
\forall a:Univ.
\forall compose:\forall _:Univ.\forall _:Univ.Univ.
\forall mocking_bird:Univ.
\forall response:\forall _:Univ.\forall _:Univ.Univ.
\forall H0:\forall A:Univ.\forall B:Univ.\forall C:Univ.eq Univ (response (compose A B) C) (response A (response B C)).
\forall H1:\forall A:Univ.eq Univ (response mocking_bird A) (response A A).\exist A:Univ.\exist B:Univ.eq Univ (response a A) B
.
intros.
exists[
2:
exists[
2:
autobatch paramodulation timeout=100;]]
assumption.
print proofterm.
qed.
(* -------------------------------------------------------------------------- *)
