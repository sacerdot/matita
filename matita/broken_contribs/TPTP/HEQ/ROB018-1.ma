set "baseuri" "cic:/matita/TPTP/ROB018-1".
include "logic/equality.ma".

(* Inclusion of: ROB018-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : ROB018-1 : TPTP v3.2.0. Released v1.0.0. *)

(*  Domain   : Robbins Algebra *)

(*  Problem  : If -(d + e) = -e then e + 2(d + -(d + -e)) absorbs d + -(d + -e) *)

(*  Version  : [Win90] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [Win90] Winker (1990), Robbins Algebra: Conditions that make a *)

(*  Source   : [Win90] *)

(*  Names    : Corollary 3.9 [Win90] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.57 v3.1.0, 0.78 v2.7.0, 0.67 v2.6.0, 0.86 v2.5.0, 1.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :    9 (   0 non-Horn;   7 unit;   4 RR) *)

(*             Number of atoms       :   11 (   7 equality) *)

(*             Maximal clause size   :    2 (   1 average) *)

(*             Number of predicates  :    2 (   0 propositional; 1-2 arity) *)

(*             Number of functors    :    7 (   3 constant; 0-2 arity) *)

(*             Number of variables   :   11 (   0 singleton) *)

(*             Maximal term depth    :    7 (   3 average) *)

(*  Comments : This could be done with the second part, together *)

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

(* ----Include axioms for numbers in Robbins algebras  *)

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
theorem prove_result:
 ∀Univ:Set.∀V:Univ.∀X:Univ.∀Y:Univ.∀Z:Univ.∀add:∀_:Univ.∀_:Univ.Univ.∀d:Univ.∀e:Univ.∀multiply:∀_:Univ.∀_:Univ.Univ.∀negate:∀_:Univ.Univ.∀one:Univ.∀positive_integer:∀_:Univ.Prop.∀successor:∀_:Univ.Univ.∀H0:eq Univ (negate (add d (negate e))) (negate e).∀H1:∀X:Univ.∀_:positive_integer X.positive_integer (successor X).∀H2:positive_integer one.∀H3:∀V:Univ.∀X:Univ.∀_:positive_integer X.eq Univ (multiply (successor V) X) (add X (multiply V X)).∀H4:∀X:Univ.eq Univ (multiply one X) X.∀H5:∀X:Univ.∀Y:Univ.eq Univ (negate (add (negate (add X Y)) (negate (add X (negate Y))))) X.∀H6:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (add (add X Y) Z) (add X (add Y Z)).∀H7:∀X:Univ.∀Y:Univ.eq Univ (add X Y) (add Y X).eq Univ (add e (multiply (successor (successor one)) (add d (negate (add d (negate e)))))) (add e (multiply (successor one) (add d (negate (add d (negate e))))))
.
intros.
autobatch depth=5 width=5 size=20 timeout=10;
try assumption.
print proofterm.
qed.

(* -------------------------------------------------------------------------- *)
