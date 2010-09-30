set "baseuri" "cic:/matita/TPTP/ROB006-3".
include "logic/equality.ma".

(* Inclusion of: ROB006-3.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : ROB006-3 : TPTP v3.2.0. Released v1.0.0. *)

(*  Domain   : Robbins Algebra *)

(*  Problem  : c + d=d => Boolean *)

(*  Version  : [Win90] (equality) axioms : Augmented. *)

(*             Theorem formulation : Denies Huntington's axiom. *)

(*  English  : If there are elements c and d such that c+d=d, then the  *)

(*             algebra is Boolean. *)

(*  Refs     : [HMT71] Henkin et al. (1971), Cylindrical Algebras *)

(*           : [Win90] Winker (1990), Robbins Algebra: Conditions that make a *)

(*           : [Wos92] Wos (1992), An Opportunity to Test Your Skills, and th *)

(*  Source   : [Wos92] *)

(*  Names    : Theorem 1.1 [Win90] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.86 v3.1.0, 1.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :   13 (   0 non-Horn;   8 unit;   8 RR) *)

(*             Number of atoms       :   19 (  14 equality) *)

(*             Maximal clause size   :    3 (   1 average) *)

(*             Number of predicates  :    2 (   0 propositional; 1-2 arity) *)

(*             Number of functors    :    9 (   5 constant; 0-2 arity) *)

(*             Number of variables   :   19 (   0 singleton) *)

(*             Maximal term depth    :    8 (   3 average) *)

(*  Comments : Commutativity, associativity, and Huntington's axiom  *)

(*             axiomatize Boolean algebra. *)

(*           : The extra lemmas are suggested by Winker (1990). *)

(* -------------------------------------------------------------------------- *)

(* ----Include axioms for Robbins algebra  *)

(* Inclusion of: Axioms/ROB001-0.ax *)

(* -------------------------------------------------------------------------- *)

(*  File     : ROB001-0 : TPTP v3.2.0. Released v1.0.0. *)

(*  Domain   : Robbins algebra *)

(*  Axioms   : Robbins algebra axioms *)

(*  Version  : [Win90] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [HMT71] Henkin et al. (1971), Cylindrical Algebras *)

(*           : [Win90] Winker (1990), Robbins Algebra: Conditions that make a *)

(*  Source   : [OTTER] *)

(*  Names    : Lemma 2.2 [Win90] *)

(*  Status   :  *)

(*  Syntax   : Number of clauses    :    3 (   0 non-Horn;   3 unit;   0 RR) *)

(*             Number of literals   :    3 (   3 equality) *)

(*             Maximal clause size  :    1 (   1 average) *)

(*             Number of predicates :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors   :    2 (   0 constant; 1-2 arity) *)

(*             Number of variables  :    7 (   0 singleton) *)

(*             Maximal term depth   :    6 (   3 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)

(* ----Include axioms for Robbins algebra numbers  *)

(* Inclusion of: Axioms/ROB001-1.ax *)

(* -------------------------------------------------------------------------- *)

(*  File     : ROB001-1 : TPTP v3.2.0. Released v1.0.0. *)

(*  Domain   : Robbins Algebra *)

(*  Axioms   : Robbins algebra numbers axioms *)

(*  Version  : [Win90] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [HMT71] Henkin et al. (1971), Cylindrical Algebras *)

(*           : [Win90] Winker (1990), Robbins Algebra: Conditions that make a *)

(*  Source   : [Win90] *)

(*  Names    :  *)

(*  Status   :  *)

(*  Syntax   : Number of clauses    :    4 (   0 non-Horn;   2 unit;   2 RR) *)

(*             Number of literals   :    6 (   2 equality) *)

(*             Maximal clause size  :    2 (   2 average) *)

(*             Number of predicates :    2 (   0 propositional; 1-2 arity) *)

(*             Number of functors   :    4 (   1 constant; 0-2 arity) *)

(*             Number of variables  :    4 (   0 singleton) *)

(*             Maximal term depth   :    3 (   2 average) *)

(*  Comments : Requires ROB001-0.ax *)

(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)

(* ----The following are extra lemmas  *)

(* ----Hypothesis of the theorem  *)
theorem prove_huntingtons_axiom:
 ∀Univ:Set.∀V:Univ.∀V2:Univ.∀X:Univ.∀Y:Univ.∀Z:Univ.∀a:Univ.∀add:∀_:Univ.∀_:Univ.Univ.∀b:Univ.∀c:Univ.∀d:Univ.∀multiply:∀_:Univ.∀_:Univ.Univ.∀negate:∀_:Univ.Univ.∀one:Univ.∀positive_integer:∀_:Univ.Prop.∀successor:∀_:Univ.Univ.∀H0:eq Univ (add c d) d.∀H1:∀X:Univ.∀Y:Univ.∀_:eq Univ (negate (add (negate Y) (negate (add X (negate Y))))) X.eq Univ (add Y (multiply (successor (successor one)) (add X (negate (add X (negate Y)))))) (add Y (multiply (successor one) (add X (negate (add X (negate Y)))))).∀H2:∀X:Univ.∀Y:Univ.∀_:eq Univ (negate (add X (negate Y))) (negate Y).eq Univ (add Y (multiply (successor (successor one)) (add X (negate (add X (negate Y)))))) (add Y (multiply (successor one) (add X (negate (add X (negate Y)))))).∀H3:∀V2:Univ.∀X:Univ.∀Y:Univ.∀_:positive_integer V2.∀_:eq Univ (negate (add X Y)) (negate Y).eq Univ (negate (add Y (multiply V2 (add X (negate (add X (negate Y))))))) (negate Y).∀H4:∀X:Univ.eq Univ (add X X) X.∀H5:∀X:Univ.∀_:positive_integer X.positive_integer (successor X).∀H6:positive_integer one.∀H7:∀V:Univ.∀X:Univ.∀_:positive_integer X.eq Univ (multiply (successor V) X) (add X (multiply V X)).∀H8:∀X:Univ.eq Univ (multiply one X) X.∀H9:∀X:Univ.∀Y:Univ.eq Univ (negate (add (negate (add X Y)) (negate (add X (negate Y))))) X.∀H10:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (add (add X Y) Z) (add X (add Y Z)).∀H11:∀X:Univ.∀Y:Univ.eq Univ (add X Y) (add Y X).eq Univ (add (negate (add a (negate b))) (negate (add (negate a) (negate b)))) b
.
intros.
autobatch depth=5 width=5 size=20 timeout=10;
try assumption.
print proofterm.
qed.

(* -------------------------------------------------------------------------- *)
