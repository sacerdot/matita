set "baseuri" "cic:/matita/TPTP/COL042-2".
include "logic/equality.ma".

(* Inclusion of: COL042-2.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : COL042-2 : TPTP v3.2.0. Released v1.2.0. *)

(*  Domain   : Combinatory Logic *)

(*  Problem  : Strong fixed point for B and W1 *)

(*  Version  : [WM88] (equality) axioms : Augmented > Especial. *)

(*             Theorem formulation : The fixed point is provided and checked. *)

(*  English  : The strong fixed point property holds for the set  *)

(*             P consisting of the combinators B and W1, where ((Bx)y)z  *)

(*             = x(yz), (W1x)y = (yx)x. *)

(*  Refs     : [WM88]  Wos & McCune (1988), Challenge Problems Focusing on Eq *)

(*           : [Wos93] Wos (1993), The Kernel Strategy and Its Use for the St *)

(*  Source   : [TPTP] *)

(*  Names    :  *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.43 v3.2.0, 0.29 v3.1.0, 0.22 v2.7.0, 0.17 v2.6.0, 0.14 v2.5.0, 0.20 v2.4.0, 0.33 v2.3.0, 0.50 v2.2.1, 0.62 v2.2.0, 0.67 v2.1.0, 0.67 v2.0.0 *)

(*  Syntax   : Number of clauses     :    4 (   0 non-Horn;   3 unit;   2 RR) *)

(*             Number of atoms       :    5 (   3 equality) *)

(*             Maximal clause size   :    2 (   1 average) *)

(*             Number of predicates  :    2 (   0 propositional; 1-2 arity) *)

(*             Number of functors    :    4 (   3 constant; 0-2 arity) *)

(*             Number of variables   :    6 (   0 singleton) *)

(*             Maximal term depth    :    8 (   3 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)
theorem prove_strong_fixed_point:
 ∀Univ:Set.∀Strong_fixed_point:Univ.∀X:Univ.∀Y:Univ.∀Z:Univ.∀apply:∀_:Univ.∀_:Univ.Univ.∀b:Univ.∀fixed_point:∀_:Univ.Prop.∀fixed_pt:Univ.∀w1:Univ.∀H0:∀Strong_fixed_point:Univ.∀_:eq Univ (apply Strong_fixed_point fixed_pt) (apply fixed_pt (apply Strong_fixed_point fixed_pt)).fixed_point Strong_fixed_point.∀H1:∀X:Univ.∀Y:Univ.eq Univ (apply (apply w1 X) Y) (apply (apply Y X) X).∀H2:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply b X) Y) Z) (apply X (apply Y Z)).fixed_point (apply (apply b (apply (apply b (apply (apply b (apply w1 w1)) (apply b w1))) b)) b)
.
intros.
autobatch depth=5 width=5 size=20 timeout=10;
try assumption.
print proofterm.
qed.

(* -------------------------------------------------------------------------- *)
