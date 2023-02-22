
include "logic/equality.ma".
(* Inclusion of: GRP011-4.p *)
(* -------------------------------------------------------------------------- *)
(*  File     : GRP011-4 : TPTP v3.1.1. Released v1.0.0. *)
(*  Domain   : Group Theory *)
(*  Problem  : Left cancellation *)
(*  Version  : [Wos65] (equality) axioms : Incomplete. *)
(*  English  :  *)
(*  Refs     : [Wos65] Wos (1965), Unpublished Note *)
(*           : [Pel86] Pelletier (1986), Seventy-five Problems for Testing Au *)
(*  Source   : [Pel86] *)
(*  Names    : Pelletier 63 [Pel86] *)
(*  Status   : Unsatisfiable *)
(*  Rating   : 0.00 v2.2.1, 0.22 v2.2.0, 0.29 v2.1.0, 0.25 v2.0.0 *)
(*  Syntax   : Number of clauses     :    5 (   0 non-Horn;   5 unit;   2 RR) *)
(*             Number of atoms       :    5 (   5 equality) *)
(*             Maximal clause size   :    1 (   1 average) *)
(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors    :    6 (   4 constant; 0-2 arity) *)
(*             Number of variables   :    5 (   0 singleton) *)
(*             Maximal term depth    :    3 (   2 average) *)
(*  Comments : [Pel86] says "... problems, published I think, by Larry Wos *)
(*             (but I cannot locate where)." *)
(* -------------------------------------------------------------------------- *)
(* ----The operation '*' is associative  *)
(* ----There exists an identity element  *)
theorem prove_left_cancellation:
 \forall Univ:Set.
\forall b:Univ.
\forall c:Univ.
\forall d:Univ.
\forall identity:Univ.
\forall inverse:\forall _:Univ.Univ.
\forall multiply:\forall _:Univ.\forall _:Univ.Univ.
\forall H0:eq Univ (multiply b c) (multiply d c).
\forall H1:\forall X:Univ.eq Univ (multiply (inverse X) X) identity.
\forall H2:\forall X:Univ.eq Univ (multiply identity X) X.
\forall H3:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (multiply (multiply X Y) Z) (multiply X (multiply Y Z)).eq Univ b d
.
intros.
autobatch paramodulation timeout=100;
try assumption.
print proofterm.
qed.
(* -------------------------------------------------------------------------- *)
