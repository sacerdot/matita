set "baseuri" "cic:/matita/TPTP/HWC002-1".
include "logic/equality.ma".

(* Inclusion of: HWC002-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : HWC002-1 : TPTP v3.2.0. Released v1.1.0. *)

(*  Domain   : Hardware Creation *)

(*  Problem  : Interchange inputs to outputs *)

(*  Version  : [ANL] axioms. *)

(*  English  : Design a circuit with inputs x and y whose outputs are y and  *)

(*             x, and contains no crossings of wires *)

(*  Refs     : [WO+92] Wos et al. (1992), Automated Reasoning: Introduction a *)

(*  Source   : [ANL] *)

(*  Names    : interchange.ver1.clauses [ANL] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.29 v3.1.0, 0.56 v2.7.0, 0.17 v2.6.0, 0.29 v2.5.0, 0.00 v2.4.0, 0.17 v2.2.1, 0.56 v2.2.0, 0.57 v2.1.0, 1.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :   38 (   0 non-Horn;  23 unit;  30 RR) *)

(*             Number of atoms       :   53 (  20 equality) *)

(*             Maximal clause size   :    2 (   1 average) *)

(*             Number of predicates  :    2 (   0 propositional; 2-3 arity) *)

(*             Number of functors    :   11 (   3 constant; 0-4 arity) *)

(*             Number of variables   :   99 (   1 singleton) *)

(*             Maximal term depth    :    4 (   2 average) *)

(*  Comments : We represent the circuit built up so far by circuit(top(X),  *)

(*             middle(Y),bottom(Z)), where top and bottom are lists of *)

(*             outputs, counting outward from the middle. *)

(*           : The original uses the equality clauses as demodulators. *)

(* -------------------------------------------------------------------------- *)

(* ----Include definitions of AND, OR and NOT  *)

(* Inclusion of: Axioms/HWC001-0.ax *)

(* -------------------------------------------------------------------------- *)

(*  File     : HWC001-0 : TPTP v3.2.0. Released v1.0.0. *)

(*  Domain   : Hardware Creation *)

(*  Axioms   : Definitions of AND, OR and NOT *)

(*  Version  : [WO+92] axioms. *)

(*             Axiom formulation : Ground axioms. *)

(*  English  :  *)

(*  Refs     : [WO+92] Wos et al. (1992), Automated Reasoning: Introduction a *)

(*  Source   : [ANL] *)

(*  Names    :  *)

(*  Status   :  *)

(*  Syntax   : Number of clauses    :   10 (   0 non-Horn;  10 unit;  10 RR) *)

(*             Number of literals   :   10 (  10 equality) *)

(*             Maximal clause size  :    1 (   1 average) *)

(*             Number of predicates :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors   :    5 (   2 constant; 0-2 arity) *)

(*             Number of variables  :    0 (   0 singleton) *)

(*             Maximal term depth   :    2 (   2 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)

(* ----Problem axioms Split the middle, keeping the middle  *)

(* ----Split the middle, omitting the middle  *)

(* ----Join across the middle if it is empty, not keeping the sides  *)

(* ----Join across the middle, keeping the sides  *)

(* ----Join to middle, keeping the sides  *)

(* ----Join the two wires nearest the middle  *)

(* ----Put inverter on the middle wire  *)

(* ----Put inverter on the adjacent wires  *)

(* ----Subsumer to get rid of circuits which are the same on top and bottom  *)

(* ----Cannot construct the answer  *)
theorem prove_output_configuration:
 ∀Univ:Set.∀X:Univ.∀X1:Univ.∀X2:Univ.∀X3:Univ.∀X4:Univ.∀Y:Univ.∀Y1:Univ.∀Y2:Univ.∀Y3:Univ.∀Y4:Univ.∀Z:Univ.∀Z1:Univ.∀Z2:Univ.∀Z3:Univ.∀myand:∀_:Univ.∀_:Univ.Univ.∀bottom:∀_:Univ.Univ.∀circuit:∀_:Univ.∀_:Univ.∀_:Univ.Prop.∀connect:∀_:Univ.∀_:Univ.Univ.∀middle:∀_:Univ.Univ.∀n0:Univ.∀n1:Univ.∀nil:Univ.∀not:∀_:Univ.Univ.∀or:∀_:Univ.∀_:Univ.Univ.∀table:∀_:Univ.∀_:Univ.∀_:Univ.∀_:Univ.Univ.∀top:∀_:Univ.Univ.∀H0:circuit (top (connect (table n0 n0 n1 n1) nil)) nil (bottom (connect (table n0 n1 n0 n1) nil)).∀H1:∀X:Univ.∀Y:Univ.eq Univ (connect X (connect X Y)) (connect X Y).∀H2:∀X:Univ.eq Univ (connect nil X) X.∀H3:eq Univ (table n1 n1 n1 n1) nil.∀H4:eq Univ (table n0 n0 n0 n0) nil.∀H5:eq Univ (not nil) nil.∀H6:∀X1:Univ.∀X2:Univ.∀X3:Univ.∀X4:Univ.eq Univ (not (table X1 X2 X3 X4)) (table (not X1) (not X2) (not X3) (not X4)).∀H7:∀X:Univ.eq Univ (or nil X) X.∀H8:∀X1:Univ.∀X2:Univ.∀X3:Univ.∀X4:Univ.∀Y1:Univ.∀Y2:Univ.∀Y3:Univ.∀Y4:Univ.eq Univ (or (table X1 X2 X3 X4) (table Y1 Y2 Y3 Y4)) (table (or X1 Y1) (or X2 Y2) (or X3 Y3) (or X4 Y4)).∀H9:∀X:Univ.eq Univ (myand nil X) X.∀H10:∀X1:Univ.∀X2:Univ.∀X3:Univ.∀X4:Univ.∀Y1:Univ.∀Y2:Univ.∀Y3:Univ.∀Y4:Univ.eq Univ (myand (table X1 X2 X3 X4) (table Y1 Y2 Y3 Y4)) (table (myand X1 Y1) (myand X2 Y2) (myand X3 Y3) (myand X4 Y4)).∀H11:∀X:Univ.∀Y:Univ.circuit (top X) Y (bottom X).∀H12:∀X1:Univ.∀X2:Univ.∀Z1:Univ.∀Z2:Univ.∀_:circuit (top (connect X1 X2)) nil (bottom (connect Z1 Z2)).circuit (top (connect (not X1) X2)) nil (bottom (connect (not Z1) Z2)).∀H13:∀X1:Univ.∀X2:Univ.∀Y:Univ.∀Z1:Univ.∀Z2:Univ.∀_:circuit (top (connect X1 X2)) (middle Y) (bottom (connect Z1 Z2)).circuit (top (connect (not X1) X2)) (middle Y) (bottom (connect (not Z1) Z2)).∀H14:∀X:Univ.∀Y:Univ.∀Z:Univ.∀_:circuit (top X) (middle Y) (bottom Z).circuit (top X) (middle (not Y)) (bottom Z).∀H15:∀X1:Univ.∀X2:Univ.∀X3:Univ.∀Y:Univ.∀Z1:Univ.∀Z2:Univ.∀Z3:Univ.∀_:circuit (top (connect X1 (connect X2 X3))) (middle Y) (bottom (connect Z1 (connect Z2 Z3))).circuit (top (connect (or X1 X2) X3)) (middle Y) (bottom (connect (or Z1 Z2) Z3)).∀H16:∀X1:Univ.∀X2:Univ.∀X3:Univ.∀Y:Univ.∀Z1:Univ.∀Z2:Univ.∀Z3:Univ.∀_:circuit (top (connect X1 (connect X2 X3))) (middle Y) (bottom (connect Z1 (connect Z2 Z3))).circuit (top (connect (myand X1 X2) X3)) (middle Y) (bottom (connect (myand Z1 Z2) Z3)).∀H17:∀X1:Univ.∀X2:Univ.∀Y:Univ.∀Z1:Univ.∀Z2:Univ.∀_:circuit (top (connect X1 X2)) (middle Y) (bottom (connect Z1 Z2)).circuit (top (connect (or Y X1) (connect X1 X2))) nil (bottom (connect (or Y Z1) (connect Z1 Z2))).∀H18:∀X1:Univ.∀X2:Univ.∀Y:Univ.∀Z1:Univ.∀Z2:Univ.∀_:circuit (top (connect X1 X2)) (middle Y) (bottom (connect Z1 Z2)).circuit (top (connect (myand Y X1) (connect X1 X2))) nil (bottom (connect (myand Y Z1) (connect Z1 Z2))).∀H19:∀X1:Univ.∀X2:Univ.∀Y1:Univ.∀Y2:Univ.∀_:circuit (top (connect X1 X2)) nil (bottom (connect Y1 Y2)).circuit (top (connect X1 X2)) (middle (or X1 Y1)) (bottom (connect Y1 Y2)).∀H20:∀X1:Univ.∀X2:Univ.∀Y1:Univ.∀Y2:Univ.∀_:circuit (top (connect X1 X2)) nil (bottom (connect Y1 Y2)).circuit (top (connect X1 X2)) (middle (myand X1 Y1)) (bottom (connect Y1 Y2)).∀H21:∀X1:Univ.∀X2:Univ.∀Y1:Univ.∀Y2:Univ.∀_:circuit (top (connect X1 X2)) nil (bottom (connect Y1 Y2)).circuit (top X2) (middle (or X1 Y1)) (bottom Y2).∀H22:∀X1:Univ.∀X2:Univ.∀Y1:Univ.∀Y2:Univ.∀_:circuit (top (connect X1 X2)) nil (bottom (connect Y1 Y2)).circuit (top X2) (middle (myand X1 Y1)) (bottom Y2).∀H23:∀X1:Univ.∀X2:Univ.∀Y:Univ.∀Z1:Univ.∀Z2:Univ.∀_:circuit (top (connect X1 X2)) (middle Y) (bottom (connect Z1 Z2)).circuit (top (connect (or Y X1) X2)) nil (bottom (connect (or Y Z1) Z2)).∀H24:∀X1:Univ.∀X2:Univ.∀Y:Univ.∀Z1:Univ.∀Z2:Univ.∀_:circuit (top (connect X1 X2)) (middle Y) (bottom (connect Z1 Z2)).circuit (top (connect (myand Y X1) X2)) nil (bottom (connect (myand Y Z1) Z2)).∀H25:∀X1:Univ.∀X2:Univ.∀Y:Univ.∀Z1:Univ.∀Z2:Univ.∀_:circuit (top (connect X1 X2)) (middle Y) (bottom (connect Z1 Z2)).circuit (top (connect (or Y X1) X2)) (middle Y) (bottom (connect (or Y Z1) Z2)).∀H26:∀X1:Univ.∀X2:Univ.∀Y:Univ.∀Z1:Univ.∀Z2:Univ.∀_:circuit (top (connect X1 X2)) (middle Y) (bottom (connect Z1 Z2)).circuit (top (connect (myand Y X1) X2)) (middle Y) (bottom (connect (myand Y Z1) Z2)).∀H27:eq Univ (not n1) n0.∀H28:eq Univ (not n0) n1.∀H29:eq Univ (or n1 n1) n1.∀H30:eq Univ (or n1 n0) n1.∀H31:eq Univ (or n0 n1) n1.∀H32:eq Univ (or n0 n0) n0.∀H33:eq Univ (myand n1 n1) n1.∀H34:eq Univ (myand n1 n0) n0.∀H35:eq Univ (myand n0 n1) n0.∀H36:eq Univ (myand n0 n0) n0.circuit (top (connect (table n0 n1 n0 n1) nil)) nil (bottom (connect (table n0 n0 n1 n1) nil))
.
intros.
autobatch depth=5 width=5 size=20 timeout=10;
try assumption.
print proofterm.
qed.

(* -------------------------------------------------------------------------- *)
