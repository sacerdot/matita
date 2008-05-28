
include "logic/equality.ma".
(* Inclusion of: GRP206-1.p *)
(* -------------------------------------------------------------------------- *)
(*  File     : GRP206-1 : TPTP v3.1.1. Released v2.3.0. *)
(*  Domain   : Group Theory (Loops) *)
(*  Problem  : In Loops, Moufang-4 => Moufang-1. *)
(*  Version  : [MP96] (equality) axioms. *)
(*  English  :  *)
(*  Refs     : [Wos96] Wos (1996), OTTER and the Moufang Identity Problem *)
(*  Source   : [Wos96] *)
(*  Names    : - [Wos96] *)
(*  Status   : Unsatisfiable *)
(*  Rating   : 0.00 v2.3.0 *)
(*  Syntax   : Number of clauses     :   10 (   0 non-Horn;  10 unit;   1 RR) *)
(*             Number of atoms       :   10 (  10 equality) *)
(*             Maximal clause size   :    1 (   1 average) *)
(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors    :    9 (   4 constant; 0-2 arity) *)
(*             Number of variables   :   15 (   0 singleton) *)
(*             Maximal term depth    :    4 (   2 average) *)
(*  Comments : *)
(* -------------------------------------------------------------------------- *)
(* ----Loop axioms: *)
(* ----Moufang-4 *)
(* ----Denial of Moufang-1 *)
theorem prove_moufang1:
 \forall Univ:Set.
\forall a:Univ.
\forall b:Univ.
\forall c:Univ.
\forall identity:Univ.
\forall left_division:\forall _:Univ.\forall _:Univ.Univ.
\forall left_inverse:\forall _:Univ.Univ.
\forall multiply:\forall _:Univ.\forall _:Univ.Univ.
\forall right_division:\forall _:Univ.\forall _:Univ.Univ.
\forall right_inverse:\forall _:Univ.Univ.
\forall H0:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (multiply X (multiply (multiply Y Z) X)) (multiply (multiply X Y) (multiply Z X)).
\forall H1:\forall X:Univ.eq Univ (multiply (left_inverse X) X) identity.
\forall H2:\forall X:Univ.eq Univ (multiply X (right_inverse X)) identity.
\forall H3:\forall X:Univ.\forall Y:Univ.eq Univ (right_division (multiply X Y) Y) X.
\forall H4:\forall X:Univ.\forall Y:Univ.eq Univ (multiply (right_division X Y) Y) X.
\forall H5:\forall X:Univ.\forall Y:Univ.eq Univ (left_division X (multiply X Y)) Y.
\forall H6:\forall X:Univ.\forall Y:Univ.eq Univ (multiply X (left_division X Y)) Y.
\forall H7:\forall X:Univ.eq Univ (multiply X identity) X.
\forall H8:\forall X:Univ.eq Univ (multiply identity X) X.eq Univ (multiply (multiply a (multiply b c)) a) (multiply (multiply a b) (multiply c a))
.
intros.
autobatch paramodulation timeout=100;
try assumption.
print proofterm.
qed.
(* -------------------------------------------------------------------------- *)
