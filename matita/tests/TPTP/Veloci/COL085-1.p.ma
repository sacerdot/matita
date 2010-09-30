
include "logic/equality.ma".
(* Inclusion of: COL085-1.p *)
(* -------------------------------------------------------------------------- *)
(*  File     : COL085-1 : TPTP v3.1.1. Released v2.6.0. *)
(*  Domain   : Combinatory Logic *)
(*  Problem  : Happy Birds, part 1 *)
(*  Version  : Especial. *)
(*  English  :  *)
(*  Refs     : [Smu85] Smullyan (1978), To Mock a Mocking Bird and Other Logi *)
(*  Source   : [TPTP] *)
(*  Names    :  *)
(*  Status   : Unsatisfiable *)
(*  Rating   : 0.00 v2.6.0 *)
(*  Syntax   : Number of clauses     :    2 (   0 non-Horn;   2 unit;   2 RR) *)
(*             Number of atoms       :    2 (   2 equality) *)
(*             Maximal clause size   :    1 (   1 average) *)
(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors    :    3 (   2 constant; 0-2 arity) *)
(*             Number of variables   :    2 (   2 singleton) *)
(*             Maximal term depth    :    2 (   2 average) *)
(*  Comments : A UEQ part of COL055-1 *)
(* -------------------------------------------------------------------------- *)
theorem prove_happiness_1:
 \forall Univ:Set.
\forall a:Univ.
\forall b:Univ.
\forall response:\forall _:Univ.\forall _:Univ.Univ.
\forall H0:eq Univ (response a b) b.\exist A:Univ.\exist B:Univ.eq Univ (response a A) B
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
