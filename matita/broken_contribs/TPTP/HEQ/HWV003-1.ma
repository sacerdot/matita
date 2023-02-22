set "baseuri" "cic:/matita/TPTP/HWV003-1".
include "logic/equality.ma".

(* Inclusion of: HWV003-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : HWV003-1 : TPTP v3.2.0. Released v1.1.0. *)

(*  Domain   : Hardware Verification *)

(*  Problem  : One bit Full Adder *)

(*  Version  : [WO+92] axioms. *)

(*  English  :  *)

(*  Refs     : [WO+92] Wos et al. (1992), Automated Reasoning: Introduction a *)

(*  Source   : [WO+92] *)

(*  Names    : - [WO+92] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.29 v3.1.0, 0.67 v2.7.0, 0.50 v2.6.0, 0.86 v2.5.0, 0.80 v2.4.0, 0.83 v2.3.0, 1.00 v2.2.1, 0.89 v2.2.0, 0.86 v2.1.0, 1.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :   47 (   0 non-Horn;  47 unit;  13 RR) *)

(*             Number of atoms       :   47 (  45 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    2 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :   20 (  14 constant; 0-3 arity) *)

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
 ∀Univ:Set.∀X:Univ.∀X1:Univ.∀X2:Univ.∀X3:Univ.∀Y:Univ.∀Z:Univ.∀a:Univ.∀a11:Univ.∀a12:Univ.∀a13:Univ.∀a14:Univ.∀a15:Univ.∀a16:Univ.∀a17:Univ.∀myand:∀_:Univ.∀_:Univ.Univ.∀b:Univ.∀c1:Univ.∀carryin:Univ.∀carryout:∀_:Univ.∀_:Univ.∀_:Univ.Univ.∀circuit:∀_:Univ.∀_:Univ.Prop.∀n0:Univ.∀n1:Univ.∀not:∀_:Univ.Univ.∀or:∀_:Univ.∀_:Univ.Univ.∀s1:Univ.∀sum:∀_:Univ.∀_:Univ.∀_:Univ.Univ.∀xor:∀_:Univ.∀_:Univ.Univ.∀H0:circuit s1 c1.∀H1:eq Univ c1 (not (myand a11 a15)).∀H2:eq Univ s1 (not (myand a16 a17)).∀H3:eq Univ a17 (not (myand a15 carryin)).∀H4:eq Univ a16 (not (myand a14 a15)).∀H5:eq Univ a15 (not (myand a14 carryin)).∀H6:eq Univ a14 (not (myand a12 a13)).∀H7:eq Univ a13 (not (myand a11 b)).∀H8:eq Univ a12 (not (myand a11 a)).∀H9:eq Univ a11 (not (myand a b)).∀H10:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (sum X Y Z) (xor (xor X Y) Z).∀H11:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (carryout X Y Z) (or (myand X (or Y Z)) (myand (not X) (myand Y Z))).∀H12:∀X:Univ.∀Y:Univ.eq Univ (xor X Y) (or (myand X (not Y)) (myand Y (not X))).∀H13:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (or (myand (myand X Y) (not Z)) (myand X Z)) (or (myand X Y) (myand X Z)).∀H14:∀X:Univ.∀Y:Univ.eq Univ (or (myand (not X) (not Y)) Y) (or Y (not X)).∀H15:∀X:Univ.∀Y:Univ.eq Univ (or (myand X (not Y)) Y) (or X Y).∀H16:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (or (or X (myand Y Z)) Z) (or X Z).∀H17:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (or (or (myand X Y) Z) Y) (or Z Y).∀H18:∀X:Univ.∀Y:Univ.eq Univ (or (myand X Y) X) X.∀H19:∀X:Univ.∀Y:Univ.eq Univ (or (myand X Y) Y) Y.∀H20:∀X1:Univ.∀X2:Univ.∀X3:Univ.eq Univ (myand (myand (myand X1 X2) X3) (not X2)) n0.∀H21:∀X1:Univ.∀X2:Univ.∀X3:Univ.eq Univ (myand (myand (myand X1 X2) X3) (not X1)) n0.∀H22:∀X:Univ.∀Y:Univ.eq Univ (or (or X Y) Y) (or X Y).∀H23:∀X:Univ.∀Y:Univ.eq Univ (myand (myand X Y) Y) (myand X Y).∀H24:∀X:Univ.∀Y:Univ.eq Univ (or (or X Y) (not X)) n1.∀H25:∀X:Univ.∀Y:Univ.eq Univ (or (or X Y) (not Y)) n1.∀H26:∀X:Univ.∀Y:Univ.eq Univ (myand (myand X Y) (not X)) n0.∀H27:∀X:Univ.∀Y:Univ.eq Univ (myand (myand X Y) (not Y)) n0.∀H28:∀X:Univ.eq Univ (or X X) X.∀H29:∀X:Univ.eq Univ (myand X X) X.∀H30:∀X:Univ.eq Univ (or X (not X)) n1.∀H31:∀X:Univ.eq Univ (myand X (not X)) n0.∀H32:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (or (or X Y) Z) (or (or X Z) Y).∀H33:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (myand (myand X Y) Z) (myand (myand X Z) Y).∀H34:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (myand (or X Y) Z) (or (myand X Z) (myand Y Z)).∀H35:∀X:Univ.∀Y:Univ.eq Univ (or X Y) (or Y X).∀H36:∀X:Univ.∀Y:Univ.eq Univ (myand X Y) (myand Y X).∀H37:∀X:Univ.eq Univ (not (not X)) X.∀H38:∀X:Univ.∀Y:Univ.eq Univ (not (or X Y)) (myand (not X) (not Y)).∀H39:∀X:Univ.∀Y:Univ.eq Univ (not (myand X Y)) (or (not X) (not Y)).∀H40:eq Univ (not n1) n0.∀H41:eq Univ (not n0) n1.∀H42:∀X:Univ.eq Univ (or X n1) n1.∀H43:∀X:Univ.eq Univ (or X n0) X.∀H44:∀X:Univ.eq Univ (myand X n1) X.∀H45:∀X:Univ.eq Univ (myand X n0) n0.circuit (sum a b carryin) (carryout a b carryin)
.
intros.
autobatch depth=5 width=5 size=20 timeout=10;
try assumption.
print proofterm.
qed.

(* -------------------------------------------------------------------------- *)
