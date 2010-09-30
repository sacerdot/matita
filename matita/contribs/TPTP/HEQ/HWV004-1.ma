set "baseuri" "cic:/matita/TPTP/HWV004-1".
include "logic/equality.ma".

(* Inclusion of: HWV004-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : HWV004-1 : TPTP v3.2.0. Released v1.1.0. *)

(*  Domain   : Hardware Verification *)

(*  Problem  : Two bit Full Adder *)

(*  Version  : [WO+92] axioms. *)

(*  English  :  *)

(*  Refs     : [WO+92] Wos et al. (1992), Automated Reasoning: Introduction a *)

(*  Source   : [WO+92] *)

(*  Names    : - [WO+92] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.57 v3.2.0, 0.43 v3.1.0, 1.00 v2.7.0, 0.83 v2.6.0, 0.86 v2.5.0, 0.40 v2.4.0, 0.83 v2.3.0, 1.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :   41 (   0 non-Horn;  41 unit;   7 RR) *)

(*             Number of atoms       :   41 (  39 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    2 (   0 propositional; 2-3 arity) *)

(*             Number of functors    :   15 (   9 constant; 0-3 arity) *)

(*             Number of variables   :   69 (  14 singleton) *)

(*             Maximal term depth    :    4 (   2 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)

(* ----Include definitions of AND, OR and NOT  *)

(* Inclusion of: Axioms/HWC002-0.ax *)

(* -------------------------------------------------------------------------- *)

(*  File     : HWC002-0 : TPTP v3.2.0. Released v1.0.0. *)

(*  Domain   : Hardware Creation *)

(*  Axioms   : Definitions of AND, OR and NOT *)

(*  Version  : [WO+92] axioms. *)

(*             Axiom formulation : Non-ground axioms. *)

(*  English  :  *)

(*  Refs     : [WO+92] Wos et al. (1992), Automated Reasoning: Introduction a *)

(*  Source   : [ANL] *)

(*  Names    :  *)

(*  Status   :  *)

(*  Syntax   : Number of clauses    :    6 (   0 non-Horn;   6 unit;   2 RR) *)

(*             Number of literals   :    6 (   6 equality) *)

(*             Maximal clause size  :    1 (   1 average) *)

(*             Number of predicates :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors   :    5 (   2 constant; 0-2 arity) *)

(*             Number of variables  :    4 (   2 singleton) *)

(*             Maximal term depth   :    2 (   2 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)

(* ----Simplifiers  *)

(* ----Evaluators  *)

(* ----Evaluators of lists of 3 terms  *)

(* ----Simplifiers for products of 4 terms  *)

(* ----Subsumption type demodulators  *)

(* ----Karnaugh map technique  *)

(* ----Karnaugh simplifier of inside product  *)

(* ----Circuit description  *)
theorem prove_circuit:
 ∀Univ:Set.∀X:Univ.∀X1:Univ.∀X2:Univ.∀X3:Univ.∀Y:Univ.∀Z:Univ.∀a0:Univ.∀a1:Univ.∀myand:∀_:Univ.∀_:Univ.Univ.∀b0:Univ.∀b1:Univ.∀carryout:∀_:Univ.∀_:Univ.∀_:Univ.Univ.∀circuit:∀_:Univ.∀_:Univ.∀_:Univ.Prop.∀n0:Univ.∀n1:Univ.∀not:∀_:Univ.Univ.∀or:∀_:Univ.∀_:Univ.Univ.∀overflow:Univ.∀s0:Univ.∀s1:Univ.∀sum:∀_:Univ.∀_:Univ.∀_:Univ.Univ.∀xor:∀_:Univ.∀_:Univ.Univ.∀H0:circuit s0 s1 overflow.∀H1:eq Univ overflow (carryout a1 b1 (carryout a0 b0 n0)).∀H2:eq Univ s1 (sum a1 b1 (carryout a0 b0 n0)).∀H3:eq Univ s0 (sum a0 b0 n0).∀H4:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (sum X Y Z) (xor (xor X Y) Z).∀H5:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (carryout X Y Z) (or (myand X (or Y Z)) (myand (not X) (myand Y Z))).∀H6:∀X:Univ.∀Y:Univ.eq Univ (xor X Y) (or (myand X (not Y)) (myand Y (not X))).∀H7:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (or (myand (myand X Y) (not Z)) (myand X Z)) (or (myand X Y) (myand X Z)).∀H8:∀X:Univ.∀Y:Univ.eq Univ (or (myand (not X) (not Y)) Y) (or Y (not X)).∀H9:∀X:Univ.∀Y:Univ.eq Univ (or (myand X (not Y)) Y) (or X Y).∀H10:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (or (or X (myand Y Z)) Z) (or X Z).∀H11:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (or (or (myand X Y) Z) Y) (or Z Y).∀H12:∀X:Univ.∀Y:Univ.eq Univ (or (myand X Y) X) X.∀H13:∀X:Univ.∀Y:Univ.eq Univ (or (myand X Y) Y) Y.∀H14:∀X1:Univ.∀X2:Univ.∀X3:Univ.eq Univ (myand (myand (myand X1 X2) X3) (not X2)) n0.∀H15:∀X1:Univ.∀X2:Univ.∀X3:Univ.eq Univ (myand (myand (myand X1 X2) X3) (not X1)) n0.∀H16:∀X:Univ.∀Y:Univ.eq Univ (or (or X Y) Y) (or X Y).∀H17:∀X:Univ.∀Y:Univ.eq Univ (myand (myand X Y) Y) (myand X Y).∀H18:∀X:Univ.∀Y:Univ.eq Univ (or (or X Y) (not X)) n1.∀H19:∀X:Univ.∀Y:Univ.eq Univ (or (or X Y) (not Y)) n1.∀H20:∀X:Univ.∀Y:Univ.eq Univ (myand (myand X Y) (not X)) n0.∀H21:∀X:Univ.∀Y:Univ.eq Univ (myand (myand X Y) (not Y)) n0.∀H22:∀X:Univ.eq Univ (or X X) X.∀H23:∀X:Univ.eq Univ (myand X X) X.∀H24:∀X:Univ.eq Univ (or X (not X)) n1.∀H25:∀X:Univ.eq Univ (myand X (not X)) n0.∀H26:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (or (or X Y) Z) (or (or X Z) Y).∀H27:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (myand (myand X Y) Z) (myand (myand X Z) Y).∀H28:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (myand (or X Y) Z) (or (myand X Z) (myand Y Z)).∀H29:∀X:Univ.∀Y:Univ.eq Univ (or X Y) (or Y X).∀H30:∀X:Univ.∀Y:Univ.eq Univ (myand X Y) (myand Y X).∀H31:∀X:Univ.eq Univ (not (not X)) X.∀H32:∀X:Univ.∀Y:Univ.eq Univ (not (or X Y)) (myand (not X) (not Y)).∀H33:∀X:Univ.∀Y:Univ.eq Univ (not (myand X Y)) (or (not X) (not Y)).∀H34:eq Univ (not n1) n0.∀H35:eq Univ (not n0) n1.∀H36:∀X:Univ.eq Univ (or X n1) n1.∀H37:∀X:Univ.eq Univ (or X n0) X.∀H38:∀X:Univ.eq Univ (myand X n1) X.∀H39:∀X:Univ.eq Univ (myand X n0) n0.circuit (xor a0 b0) (xor (xor a1 b1) (carryout a0 b0 n0)) (or (myand a1 b1) (myand (myand a0 b0) (or a1 b1)))
.
intros.
autobatch depth=5 width=5 size=20 timeout=10;
try assumption.
print proofterm.
qed.

(* -------------------------------------------------------------------------- *)
