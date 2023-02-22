set "baseuri" "cic:/matita/TPTP/COL006-3".
include "logic/equality.ma".

(* Inclusion of: COL006-3.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : COL006-3 : TPTP v3.2.0. Released v1.0.0. *)

(*  Domain   : Combinatory Logic *)

(*  Problem  : Strong fixed point for S and K *)

(*  Version  : [WM88] (equality) axioms : Augmented > Especial. *)

(*             Theorem formulation : The fixed point is provided and checked. *)

(*  English  : The strong fixed point property holds for the set  *)

(*             P consisting of the combinators S and K alone, where *)

(*             ((Sx)y)z = (xz)(yz), (Kx)y = x. *)

(*  Refs     : [WM88]  Wos & McCune (1988), Challenge Problems Focusing on Eq *)

(*  Source   : [TPTP] *)

(*  Names    :  *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.57 v3.1.0, 0.89 v2.7.0, 0.67 v2.6.0, 0.71 v2.5.0, 0.80 v2.4.0, 0.83 v2.2.1, 0.89 v2.2.0, 0.86 v2.1.0, 1.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :    4 (   0 non-Horn;   3 unit;   2 RR) *)

(*             Number of atoms       :    5 (   3 equality) *)

(*             Maximal clause size   :    2 (   1 average) *)

(*             Number of predicates  :    2 (   0 propositional; 1-2 arity) *)

(*             Number of functors    :    4 (   3 constant; 0-2 arity) *)

(*             Number of variables   :    6 (   1 singleton) *)

(*             Maximal term depth    :    8 (   3 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)
theorem prove_strong_fixed_point:
 ∀Univ:Set.∀Strong_fixed_point:Univ.∀X:Univ.∀Y:Univ.∀Z:Univ.∀apply:∀_:Univ.∀_:Univ.Univ.∀fixed_point:∀_:Univ.Prop.∀fixed_pt:Univ.∀k:Univ.∀s:Univ.∀H0:∀Strong_fixed_point:Univ.∀_:eq Univ (apply Strong_fixed_point fixed_pt) (apply fixed_pt (apply Strong_fixed_point fixed_pt)).fixed_point Strong_fixed_point.∀H1:∀X:Univ.∀Y:Univ.eq Univ (apply (apply k X) Y) X.∀H2:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply s X) Y) Z) (apply (apply X Z) (apply Y Z)).fixed_point (apply (apply s (apply k (apply (apply s (apply (apply s k) k)) (apply (apply s k) k)))) (apply (apply s (apply (apply s (apply k s)) k)) (apply k (apply (apply s (apply (apply s k) k)) (apply (apply s k) k)))))
.
intros.
autobatch depth=5 width=5 size=20 timeout=10;
try assumption.
print proofterm.
qed.

(* -------------------------------------------------------------------------- *)
