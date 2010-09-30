set "baseuri" "cic:/matita/TPTP/LAT041-1".
include "logic/equality.ma".

(* Inclusion of: LAT041-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : LAT041-1 : TPTP v3.2.0. Released v2.4.0. *)

(*  Domain   : Lattice Theory *)

(*  Problem  : A hyperbase for type <2,2> lattice hyperidentities *)

(*  Version  : [PP00] axioms. *)

(*  English  :  *)

(*  Refs     : [PP00]  Padmanabhan & Penner (2000), A Hyperbase for Binary La *)

(*  Source   : [PP00] *)

(*  Names    :  *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.71 v3.2.0, 0.57 v3.1.0, 0.78 v2.7.0, 1.00 v2.4.0 *)

(*  Syntax   : Number of clauses     :   17 (   0 non-Horn;  14 unit;   7 RR) *)

(*             Number of atoms       :   21 (  11 equality) *)

(*             Maximal clause size   :    3 (   1 average) *)

(*             Number of predicates  :    2 (   0 propositional; 1-2 arity) *)

(*             Number of functors    :   15 (  11 constant; 0-3 arity) *)

(*             Number of variables   :   29 (   2 singleton) *)

(*             Maximal term depth    :    6 (   2 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)
theorem prove_q4:
 ∀Univ:Set.∀V:Univ.∀W:Univ.∀W1:Univ.∀W2:Univ.∀X:Univ.∀Y:Univ.∀Z:Univ.∀a:Univ.∀b:Univ.∀big_p:∀_:Univ.∀_:Univ.∀_:Univ.Univ.∀big_t:∀_:Univ.∀_:Univ.∀_:Univ.Univ.∀c:Univ.∀d:Univ.∀e:Univ.∀plus:∀_:Univ.∀_:Univ.Univ.∀term:∀_:Univ.Prop.∀term1:Univ.∀term2:Univ.∀term3:Univ.∀term4:Univ.∀term5:Univ.∀term6:Univ.∀times:∀_:Univ.∀_:Univ.Univ.∀H0:∀W1:Univ.∀W2:Univ.∀X:Univ.∀Y:Univ.∀Z:Univ.∀_:term W2.∀_:term W1.eq Univ (big_t W1 (big_p W2 (big_t W1 X Y) Z) (big_p W2 Y Z)) (big_p W2 (big_t W1 X Y) Z).∀H1:∀V:Univ.∀W:Univ.∀X:Univ.∀Y:Univ.∀Z:Univ.∀_:term W.eq Univ (big_p W (big_p W X Y) (big_p W Z V)) (big_p W (big_p W X Z) (big_p W Y V)).∀H2:∀W:Univ.∀X:Univ.∀Y:Univ.∀Z:Univ.∀_:term W.eq Univ (big_p W (big_p W X Y) Z) (big_p W X (big_p W Y Z)).∀H3:term term6.∀H4:term term5.∀H5:term term4.∀H6:term term3.∀H7:term term2.∀H8:term term1.∀H9:∀W:Univ.∀X:Univ.∀Y:Univ.eq Univ (big_t W X Y) (big_p W X Y).∀H10:∀X:Univ.∀Y:Univ.eq Univ (big_p term6 X Y) (plus Y X).∀H11:∀X:Univ.∀Y:Univ.eq Univ (big_p term5 X Y) (plus X Y).∀H12:∀X:Univ.∀Y:Univ.eq Univ (big_p term4 X Y) (times Y X).∀H13:∀X:Univ.∀Y:Univ.eq Univ (big_p term3 X Y) (times X Y).∀H14:∀X:Univ.∀Y:Univ.eq Univ (big_p term2 X Y) Y.∀H15:∀X:Univ.∀Y:Univ.eq Univ (big_p term1 X Y) X.eq Univ (times a (plus b (times d (times c e)))) (times a (plus b (times (plus b c) (times d (times c e)))))
.
intros.
autobatch depth=5 width=5 size=20 timeout=10;
try assumption.
print proofterm.
qed.

(* -------------------------------------------------------------------------- *)
