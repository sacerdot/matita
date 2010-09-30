set "baseuri" "cic:/matita/TPTP/NUM017-2".
include "logic/equality.ma".

(* Inclusion of: NUM017-2.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : NUM017-2 : TPTP v3.2.0. Bugfixed v1.2.1. *)

(*  Domain   : Number Theory *)

(*  Problem  : Square root of this prime is irrational *)

(*  Version  : [Rob63] axioms : Incomplete > Augmented > Complete. *)

(*  English  : If a is prime, and a is not b^2/c^2, then the square root  *)

(*             of a is irrational. *)

(*  Refs     : [Rob63] Robinson (1963), Theorem Proving on the Computer *)

(*  Source   : [TPTP] *)

(*  Names    :  *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v3.1.0, 0.22 v2.7.0, 0.00 v2.6.0, 0.29 v2.5.0, 0.00 v2.2.1, 0.38 v2.2.0, 0.50 v2.1.0, 0.33 v2.0.0 *)

(*  Syntax   : Number of clauses     :   15 (   0 non-Horn;   5 unit;  14 RR) *)

(*             Number of atoms       :   34 (   2 equality) *)

(*             Maximal clause size   :    4 (   2 average) *)

(*             Number of predicates  :    4 (   0 propositional; 1-3 arity) *)

(*             Number of functors    :    7 (   5 constant; 0-2 arity) *)

(*             Number of variables   :   37 (   1 singleton) *)

(*             Maximal term depth    :    2 (   1 average) *)

(*  Comments :  *)

(*  Bugfixes : v1.2.1 - Clause primes_lemma1 fixed. *)

(* -------------------------------------------------------------------------- *)
theorem prove_there_is_no_common_divisor:
 ∀Univ:Set.∀A:Univ.∀B:Univ.∀C:Univ.∀D:Univ.∀E:Univ.∀F:Univ.∀a:Univ.∀b:Univ.∀c:Univ.∀d:Univ.∀divides:∀_:Univ.∀_:Univ.Prop.∀e:Univ.∀multiply:∀_:Univ.∀_:Univ.Univ.∀prime:∀_:Univ.Prop.∀product:∀_:Univ.∀_:Univ.∀_:Univ.Prop.∀second_divided_by_1st:∀_:Univ.∀_:Univ.Univ.∀H0:product a e d.∀H1:product c c e.∀H2:product b b d.∀H3:prime a.∀H4:∀A:Univ.∀B:Univ.∀C:Univ.∀_:prime A.∀_:product C C B.∀_:divides A B.divides A C.∀H5:∀A:Univ.∀B:Univ.∀C:Univ.∀_:product A B C.divides A C.∀H6:∀A:Univ.∀B:Univ.∀_:divides A B.product A (second_divided_by_1st A B) B.∀H7:∀A:Univ.∀B:Univ.∀C:Univ.∀D:Univ.∀_:product A B D.∀_:product A B C.eq Univ D C.∀H8:∀A:Univ.∀B:Univ.∀C:Univ.∀_:divides C A.∀_:divides A B.divides C B.∀H9:∀A:Univ.∀B:Univ.∀C:Univ.∀D:Univ.∀_:product A D C.∀_:product A B C.eq Univ B D.∀H10:∀A:Univ.∀B:Univ.∀C:Univ.∀_:product A B C.product B A C.∀H11:∀A:Univ.∀B:Univ.∀C:Univ.∀D:Univ.∀E:Univ.∀F:Univ.∀_:product F D A.∀_:product D B E.∀_:product A B C.product F E C.∀H12:∀A:Univ.∀B:Univ.∀C:Univ.∀D:Univ.∀E:Univ.∀F:Univ.∀_:product A D F.∀_:product D E B.∀_:product A B C.product F E C.∀H13:∀A:Univ.∀B:Univ.product A B (multiply A B).∃A:Univ.And (divides A b) (divides A c)
.
intros.
exists[
2:
autobatch depth=5 width=5 size=20 timeout=10;
try assumption.
|
skip]
print proofterm.
qed.

(* -------------------------------------------------------------------------- *)
