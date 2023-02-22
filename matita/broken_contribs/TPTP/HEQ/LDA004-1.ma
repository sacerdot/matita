set "baseuri" "cic:/matita/TPTP/LDA004-1".
include "logic/equality.ma".

(* Inclusion of: LDA004-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : LDA004-1 : TPTP v3.2.0. Released v1.0.0. *)

(*  Domain   : LD-Algebras (Left segments) *)

(*  Problem  : Show that 3*2(U2) is a left segment of U1(U3) *)

(*  Version  : [Jec93] axioms. *)

(*  English  :  *)

(*  Refs     : [Jec93] Jech (1993), LD-Algebras *)

(*  Source   : [Jec93] *)

(*  Names    : Problem 4 [Jec93] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.57 v3.2.0, 0.43 v3.1.0, 0.56 v2.7.0, 0.50 v2.6.0, 0.43 v2.5.0, 0.40 v2.4.0, 0.67 v2.3.0, 0.83 v2.2.1, 1.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :   12 (   0 non-Horn;  11 unit;  10 RR) *)

(*             Number of atoms       :   14 (   9 equality) *)

(*             Maximal clause size   :    3 (   1 average) *)

(*             Number of predicates  :    2 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :   10 (   9 constant; 0-2 arity) *)

(*             Number of variables   :    8 (   1 singleton) *)

(*             Maximal term depth    :    3 (   2 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)

(* ----A1: x(yz)=xy(xz)  *)

(* ----x is a left segment of xy  *)

(* ----transitive  *)

(* ----3*2*U2 is a left segment of U1*U3  *)
theorem prove_equation:
 ∀Univ:Set.∀X:Univ.∀Y:Univ.∀Z:Univ.∀a:Univ.∀b:Univ.∀f:∀_:Univ.∀_:Univ.Univ.∀left:∀_:Univ.∀_:Univ.Prop.∀n1:Univ.∀n2:Univ.∀n3:Univ.∀u:Univ.∀u1:Univ.∀u2:Univ.∀u3:Univ.∀H0:eq Univ b (f u1 u3).∀H1:eq Univ a (f (f n3 n2) u2).∀H2:eq Univ u3 (f u n3).∀H3:eq Univ u2 (f u n2).∀H4:eq Univ u1 (f u n1).∀H5:eq Univ u (f n2 n2).∀H6:eq Univ n3 (f n2 n1).∀H7:eq Univ n2 (f n1 n1).∀H8:∀X:Univ.∀Y:Univ.∀Z:Univ.∀_:left Y Z.∀_:left X Y.left X Z.∀H9:∀X:Univ.∀Y:Univ.left X (f X Y).∀H10:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (f X (f Y Z)) (f (f X Y) (f X Z)).left a b
.
intros.
autobatch depth=5 width=5 size=20 timeout=10;
try assumption.
print proofterm.
qed.

(* -------------------------------------------------------------------------- *)
