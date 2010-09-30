set "baseuri" "cic:/matita/TPTP/HEN011-3".
include "logic/equality.ma".

(* Inclusion of: HEN011-3.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : HEN011-3 : TPTP v3.2.0. Released v1.0.0. *)

(*  Domain   : Henkin Models *)

(*  Problem  : This operation is commutative *)

(*  Version  : [MOW76] axioms. *)

(*  English  : Define & on the set of Z', where Z' = identity/Z,  *)

(*             by X' & Y'=X'/(identity/Y'). The operation is commutative. *)

(*  Refs     : [MOW76] McCharen et al. (1976), Problems and Experiments for a *)

(*  Source   : [ANL] *)

(*  Names    : HP11 [ANL] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.43 v3.2.0, 0.14 v3.1.0, 0.33 v2.7.0, 0.17 v2.6.0, 0.43 v2.5.0, 0.40 v2.4.0, 0.50 v2.3.0, 0.33 v2.2.1, 0.67 v2.2.0, 0.86 v2.1.0, 1.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :   13 (   0 non-Horn;  10 unit;   9 RR) *)

(*             Number of atoms       :   17 (   9 equality) *)

(*             Maximal clause size   :    3 (   1 average) *)

(*             Number of predicates  :    2 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    9 (   8 constant; 0-2 arity) *)

(*             Number of variables   :   13 (   3 singleton) *)

(*             Maximal term depth    :    4 (   2 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)

(* ----Include Henkin model axioms for equality formulation  *)

(* Inclusion of: Axioms/HEN002-0.ax *)

(* -------------------------------------------------------------------------- *)

(*  File     : HEN002-0 : TPTP v3.2.0. Released v1.0.0. *)

(*  Domain   : Henkin Models *)

(*  Axioms   : Henkin model axioms *)

(*  Version  : [MOW76] axioms. *)

(*  English  :  *)

(*  Refs     : [MOW76] McCharen et al. (1976), Problems and Experiments for a *)

(*  Source   : [ANL] *)

(*  Names    :  *)

(*  Status   :  *)

(*  Syntax   : Number of clauses    :    7 (   0 non-Horn;   4 unit;   3 RR) *)

(*             Number of literals   :   11 (   3 equality) *)

(*             Maximal clause size  :    3 (   2 average) *)

(*             Number of predicates :    2 (   0 propositional; 2-2 arity) *)

(*             Number of functors   :    3 (   2 constant; 0-2 arity) *)

(*             Number of variables  :   13 (   3 singleton) *)

(*             Maximal term depth   :    3 (   1 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)

(* ----A0: Definition of less_equal  *)

(* ----A1: x/y <= x  *)

(* ----A2: (x/z) / (y/z) <= (x/y) / z  *)

(* ----A3: 0<=x  *)

(* ----A4: x <= y and y <= x implies that x = y  *)

(* ----A5: x <= identity (Thus an implicative model with unit )  *)

(* ----Implicit in equality formulation: '/' is well defined  *)

(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
theorem prove_commutativity:
 ∀Univ:Set.∀X:Univ.∀Y:Univ.∀Z:Univ.∀a:Univ.∀b:Univ.∀c:Univ.∀d:Univ.∀divide:∀_:Univ.∀_:Univ.Univ.∀e:Univ.∀g:Univ.∀identity:Univ.∀less_equal:∀_:Univ.∀_:Univ.Prop.∀zero:Univ.∀H0:eq Univ (divide identity d) g.∀H1:eq Univ (divide identity c) e.∀H2:eq Univ (divide identity b) d.∀H3:eq Univ (divide identity a) c.∀H4:eq Univ (divide (divide identity a) (divide identity (divide identity b))) (divide (divide identity b) (divide identity (divide identity a))).∀H5:∀X:Univ.less_equal X identity.∀H6:∀X:Univ.∀Y:Univ.∀_:less_equal Y X.∀_:less_equal X Y.eq Univ X Y.∀H7:∀X:Univ.less_equal zero X.∀H8:∀X:Univ.∀Y:Univ.∀Z:Univ.less_equal (divide (divide X Z) (divide Y Z)) (divide (divide X Y) Z).∀H9:∀X:Univ.∀Y:Univ.less_equal (divide X Y) X.∀H10:∀X:Univ.∀Y:Univ.∀_:eq Univ (divide X Y) zero.less_equal X Y.∀H11:∀X:Univ.∀Y:Univ.∀_:less_equal X Y.eq Univ (divide X Y) zero.eq Univ (divide c g) (divide d e)
.
intros.
autobatch depth=5 width=5 size=20 timeout=10;
try assumption.
print proofterm.
qed.

(* -------------------------------------------------------------------------- *)
