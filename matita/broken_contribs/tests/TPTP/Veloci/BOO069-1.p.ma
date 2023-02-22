
include "logic/equality.ma".
(* Inclusion of: BOO069-1.p *)
(* -------------------------------------------------------------------------- *)
(*  File     : BOO069-1 : TPTP v3.1.1. Released v2.6.0. *)
(*  Domain   : Boolean Algebra (Ternary) *)
(*  Problem  : Ternary Boolean Algebra Single axiom is complete, part 3 *)
(*  Version  : [MP96] (equality) axioms. *)
(*  English  :  *)
(*  Refs     : [McC98] McCune (1998), Email to G. Sutcliffe *)
(*           : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq *)
(*  Source   : [TPTP] *)
(*  Names    :  *)
(*  Status   : Unsatisfiable *)
(*  Rating   : 0.00 v3.1.0, 0.11 v2.7.0, 0.00 v2.6.0 *)
(*  Syntax   : Number of clauses     :    2 (   0 non-Horn;   2 unit;   1 RR) *)
(*             Number of atoms       :    2 (   2 equality) *)
(*             Maximal clause size   :    1 (   1 average) *)
(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors    :    4 (   2 constant; 0-3 arity) *)
(*             Number of variables   :    7 (   0 singleton) *)
(*             Maximal term depth    :    5 (   2 average) *)
(*  Comments : A UEQ part of BOO035-1 *)
(* -------------------------------------------------------------------------- *)
theorem prove_tba_axioms_3:
 \forall Univ:Set.
\forall a:Univ.
\forall b:Univ.
\forall inverse:\forall _:Univ.Univ.
\forall multiply:\forall _:Univ.\forall _:Univ.\forall _:Univ.Univ.
\forall H0:\forall A:Univ.\forall B:Univ.\forall C:Univ.\forall D:Univ.\forall E:Univ.\forall F:Univ.\forall G:Univ.eq Univ (multiply (multiply A (inverse A) B) (inverse (multiply (multiply C D E) F (multiply C D G))) (multiply D (multiply G F E) C)) B.eq Univ (multiply a b (inverse b)) a
.
intros.
autobatch paramodulation timeout=100;
try assumption.
print proofterm.
qed.
(* -------------------------------------------------------------------------- *)
