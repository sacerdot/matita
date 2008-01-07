
include "logic/equality.ma".
(* Inclusion of: BOO034-1.p *)
(* -------------------------------------------------------------------------- *)
(*  File     : BOO034-1 : TPTP v3.1.1. Released v2.2.0. *)
(*  Domain   : Boolean Algebra (Ternary) *)
(*  Problem  : Ternary Boolean Algebra Single axiom is sound. *)
(*  Version  : [MP96] (equality) axioms. *)
(*  English  : We show that that an equation (which turns out to be a single *)
(*             axiom for TBA) can be derived from the axioms of TBA. *)
(*  Refs     : [McC98] McCune (1998), Email to G. Sutcliffe *)
(*           : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq *)
(*  Source   : [McC98] *)
(*  Names    : TBA-1-a [MP96] *)
(*  Status   : Unsatisfiable *)
(*  Rating   : 0.21 v3.1.0, 0.11 v2.7.0, 0.27 v2.6.0, 0.33 v2.5.0, 0.00 v2.2.1 *)
(*  Syntax   : Number of clauses     :    6 (   0 non-Horn;   6 unit;   1 RR) *)
(*             Number of atoms       :    6 (   6 equality) *)
(*             Maximal clause size   :    1 (   1 average) *)
(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors    :    9 (   7 constant; 0-3 arity) *)
(*             Number of variables   :   13 (   2 singleton) *)
(*             Maximal term depth    :    5 (   2 average) *)
(*  Comments : *)
(* -------------------------------------------------------------------------- *)
(* ----Include ternary Boolean algebra axioms *)
(* Inclusion of: Axioms/BOO001-0.ax *)
(* -------------------------------------------------------------------------- *)
(*  File     : BOO001-0 : TPTP v3.1.1. Released v1.0.0. *)
(*  Domain   : Algebra (Ternary Boolean) *)
(*  Axioms   : Ternary Boolean algebra (equality) axioms *)
(*  Version  : [OTTER] (equality) axioms. *)
(*  English  :  *)
(*  Refs     : [Wos88] Wos (1988), Automated Reasoning - 33 Basic Research Pr *)
(*           : [Win82] Winker (1982), Generation and Verification of Finite M *)
(*  Source   : [OTTER] *)
(*  Names    :  *)
(*  Status   :  *)
(*  Syntax   : Number of clauses    :    5 (   0 non-Horn;   5 unit;   0 RR) *)
(*             Number of literals   :    5 (   5 equality) *)
(*             Maximal clause size  :    1 (   1 average) *)
(*             Number of predicates :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors   :    2 (   0 constant; 1-3 arity) *)
(*             Number of variables  :   13 (   2 singleton) *)
(*             Maximal term depth   :    3 (   2 average) *)
(*  Comments : These axioms appear in [Win82], in which ternary_multiply_1 is *)
(*             shown to be independant. *)
(*           : These axioms are also used in [Wos88], p.222. *)
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
(* ----Denial of single axiom: *)
theorem prove_single_axiom:
 \forall Univ:Set.
\forall a:Univ.
\forall b:Univ.
\forall c:Univ.
\forall d:Univ.
\forall e:Univ.
\forall f:Univ.
\forall g:Univ.
\forall inverse:\forall _:Univ.Univ.
\forall multiply:\forall _:Univ.\forall _:Univ.\forall _:Univ.Univ.
\forall H0:\forall X:Univ.\forall Y:Univ.eq Univ (multiply X Y (inverse Y)) X.
\forall H1:\forall X:Univ.\forall Y:Univ.eq Univ (multiply (inverse Y) Y X) X.
\forall H2:\forall X:Univ.\forall Y:Univ.eq Univ (multiply X X Y) X.
\forall H3:\forall X:Univ.\forall Y:Univ.eq Univ (multiply Y X X) X.
\forall H4:\forall V:Univ.\forall W:Univ.\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (multiply (multiply V W X) Y (multiply V W Z)) (multiply V W (multiply X Y Z)).eq Univ (multiply (multiply a (inverse a) b) (inverse (multiply (multiply c d e) f (multiply c d g))) (multiply d (multiply g f e) c)) b
.
intros.
autobatch paramodulation timeout=100;
try assumption.
print proofterm.
qed.
(* -------------------------------------------------------------------------- *)
