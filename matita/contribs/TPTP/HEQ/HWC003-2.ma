set "baseuri" "cic:/matita/TPTP/HWC003-2".
include "logic/equality.ma".

(* Inclusion of: HWC003-2.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : HWC003-2 : TPTP v3.2.0. Released v1.1.0. *)

(*  Domain   : Hardware Creation *)

(*  Problem  : Invert 3 inputs with 2 not gates *)

(*  Version  : [WO+92] axioms. *)

(*  English  :  *)

(*  Refs     : [WO+92] Wos et al. (1992), Automated Reasoning: Introduction a *)

(*  Source   : [ANL] *)

(*  Names    : two.inverter.ver2.in [ANL] *)

(*           : - [WO+92] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.43 v3.2.0, 0.29 v3.1.0, 0.44 v2.7.0, 0.33 v2.6.0, 0.43 v2.5.0, 0.20 v2.4.0, 0.33 v2.2.1, 0.78 v2.2.0, 0.71 v2.1.0, 0.80 v2.0.0 *)

(*  Syntax   : Number of clauses     :   25 (   0 non-Horn;  19 unit;   8 RR) *)

(*             Number of atoms       :   34 (  16 equality) *)

(*             Maximal clause size   :    3 (   1 average) *)

(*             Number of predicates  :    4 (   0 propositional; 2-10 arity) *)

(*             Number of functors    :   25 (  16 constant; 0-8 arity) *)

(*             Number of variables   :   95 (   9 singleton) *)

(*             Maximal term depth    :   14 (   1 average) *)

(*  Comments : The original uses the equality axioms as demodulators. *)

(* -------------------------------------------------------------------------- *)

(* ----Include definitions of AND, OR and NOT *)

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

(* ----Problem axioms *)
theorem prove_cannot_construct_this:
 ∀Univ:Set.∀V:Univ.∀X:Univ.∀X000:Univ.∀X001:Univ.∀X010:Univ.∀X011:Univ.∀X1:Univ.∀X100:Univ.∀X101:Univ.∀X110:Univ.∀X111:Univ.∀X2:Univ.∀X3:Univ.∀X4:Univ.∀X5:Univ.∀X6:Univ.∀X7:Univ.∀X8:Univ.∀Xname:Univ.∀Xrevlist:Univ.∀Y:Univ.∀Y1:Univ.∀Y2:Univ.∀Y3:Univ.∀Y4:Univ.∀Y5:Univ.∀Y6:Univ.∀Y7:Univ.∀Y8:Univ.∀Z:Univ.∀add_inverter:∀_:Univ.∀_:Univ.Univ.∀myand:∀_:Univ.∀_:Univ.Univ.∀basic_output:∀_:Univ.∀_:Univ.∀_:Univ.∀_:Univ.∀_:Univ.∀_:Univ.∀_:Univ.∀_:Univ.∀_:Univ.Prop.∀end:Univ.∀inverter_table:∀_:Univ.∀_:Univ.∀_:Univ.∀_:Univ.∀_:Univ.∀_:Univ.∀_:Univ.∀_:Univ.Univ.∀list:∀_:Univ.∀_:Univ.Univ.∀list_reversion:∀_:Univ.∀_:Univ.Univ.∀make_reverse_list:∀_:Univ.Univ.∀n0:Univ.∀n1:Univ.∀not:∀_:Univ.Univ.∀not_reversion:Univ.∀or:∀_:Univ.∀_:Univ.Univ.∀output:∀_:Univ.∀_:Univ.∀_:Univ.∀_:Univ.∀_:Univ.∀_:Univ.∀_:Univ.∀_:Univ.∀_:Univ.Prop.∀possible_reversion:∀_:Univ.∀_:Univ.∀_:Univ.Univ.∀r00m:Univ.∀r01m:Univ.∀r0m0:Univ.∀r0m1:Univ.∀r10m:Univ.∀r11m:Univ.∀r1m0:Univ.∀r1m1:Univ.∀rm00:Univ.∀rm01:Univ.∀rm10:Univ.∀rm11:Univ.∀test:∀_:Univ.∀_:Univ.∀_:Univ.∀_:Univ.∀_:Univ.∀_:Univ.∀_:Univ.∀_:Univ.∀_:Univ.∀_:Univ.Prop.∀H0:∀X:Univ.output n0 n1 n0 n1 n0 n1 n0 n1 X.∀H1:∀X:Univ.output n0 n0 n1 n1 n0 n0 n1 n1 X.∀H2:∀X:Univ.output n0 n0 n0 n0 n1 n1 n1 n1 X.∀H3:∀V:Univ.∀X1:Univ.∀X2:Univ.∀X3:Univ.∀X4:Univ.∀X5:Univ.∀X6:Univ.∀X7:Univ.∀X8:Univ.∀Xrevlist:Univ.∀_:test X1 X2 X3 X4 X5 X6 X7 X8 V Xrevlist.basic_output X1 X2 X3 X4 X5 X6 X7 X8 V.∀H4:∀V:Univ.∀X1:Univ.∀X2:Univ.∀X3:Univ.∀X4:Univ.∀X5:Univ.∀X6:Univ.∀X7:Univ.∀X8:Univ.∀_:basic_output X1 X2 X3 X4 X5 X6 X7 X8 V.output X1 X2 X3 X4 X5 X6 X7 X8 V.∀H5:∀V:Univ.∀X1:Univ.∀X2:Univ.∀X3:Univ.∀X4:Univ.∀X5:Univ.∀X6:Univ.∀X7:Univ.∀X8:Univ.∀_:output X1 X2 X3 X4 X5 X6 X7 X8 V.test (not X1) (not X2) (not X3) (not X4) (not X5) (not X6) (not X7) (not X8) (add_inverter V (inverter_table (not X1) (not X2) (not X3) (not X4) (not X5) (not X6) (not X7) (not X8))) (make_reverse_list (list (inverter_table (not X1) (not X2) (not X3) (not X4) (not X5) (not X6) (not X7) (not X8)) V)).∀H6:∀V:Univ.∀X1:Univ.∀X2:Univ.∀X3:Univ.∀X4:Univ.∀X5:Univ.∀X6:Univ.∀X7:Univ.∀X8:Univ.∀Y1:Univ.∀Y2:Univ.∀Y3:Univ.∀Y4:Univ.∀Y5:Univ.∀Y6:Univ.∀Y7:Univ.∀Y8:Univ.∀_:output Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 V.∀_:basic_output X1 X2 X3 X4 X5 X6 X7 X8 V.output (or X1 Y1) (or X2 Y2) (or X3 Y3) (or X4 Y4) (or X5 Y5) (or X6 Y6) (or X7 Y7) (or X8 Y8) V.∀H7:∀V:Univ.∀X1:Univ.∀X2:Univ.∀X3:Univ.∀X4:Univ.∀X5:Univ.∀X6:Univ.∀X7:Univ.∀X8:Univ.∀Y1:Univ.∀Y2:Univ.∀Y3:Univ.∀Y4:Univ.∀Y5:Univ.∀Y6:Univ.∀Y7:Univ.∀Y8:Univ.∀_:basic_output Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 V.∀_:basic_output X1 X2 X3 X4 X5 X6 X7 X8 V.basic_output (myand X1 Y1) (myand X2 Y2) (myand X3 Y3) (myand X4 Y4) (myand X5 Y5) (myand X6 Y6) (myand X7 Y7) (myand X8 Y8) V.∀H8:∀X:Univ.∀Y:Univ.eq Univ (list_reversion X (list_reversion X Y)) (list_reversion X Y).∀H9:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (list_reversion X (list_reversion Y Z)) (list_reversion Y (list_reversion X Z)).∀H10:∀X:Univ.eq Univ (list_reversion not_reversion X) X.∀H11:∀X:Univ.∀Xname:Univ.eq Univ (possible_reversion Xname X X) not_reversion.∀H12:∀Xname:Univ.eq Univ (possible_reversion Xname n0 n1) not_reversion.∀H13:∀Xname:Univ.eq Univ (possible_reversion Xname n1 n0) Xname.∀H14:∀V:Univ.eq Univ (make_reverse_list V) end.∀H15:∀V:Univ.∀X000:Univ.∀X001:Univ.∀X010:Univ.∀X011:Univ.∀X100:Univ.∀X101:Univ.∀X110:Univ.∀X111:Univ.eq Univ (make_reverse_list (list (inverter_table X000 X001 X010 X011 X100 X101 X110 X111) V)) (list_reversion (possible_reversion r00m X000 X001) (list_reversion (possible_reversion r01m X010 X011) (list_reversion (possible_reversion r10m X100 X101) (list_reversion (possible_reversion r11m X110 X111) (list_reversion (possible_reversion r0m0 X000 X010) (list_reversion (possible_reversion r0m1 X001 X011) (list_reversion (possible_reversion r1m0 X100 X110) (list_reversion (possible_reversion r1m1 X101 X111) (list_reversion (possible_reversion rm00 X000 X100) (list_reversion (possible_reversion rm01 X001 X101) (list_reversion (possible_reversion rm10 X010 X110) (list_reversion (possible_reversion rm11 X011 X111) (make_reverse_list V))))))))))))).∀H16:∀X:Univ.∀Y:Univ.eq Univ (add_inverter X Y) (list Y X).∀H17:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (add_inverter (list X Y) Z) (list X (add_inverter Y Z)).∀H18:eq Univ (not n1) n0.∀H19:eq Univ (not n0) n1.∀H20:∀X:Univ.eq Univ (or X n1) n1.∀H21:∀X:Univ.eq Univ (or X n0) X.∀H22:∀X:Univ.eq Univ (myand X n1) X.∀H23:∀X:Univ.eq Univ (myand X n0) n0.∃V:Univ.And (output n1 n0 n1 n0 n1 n0 n1 n0 V) (And (output n1 n1 n0 n0 n1 n1 n0 n0 V) (output n1 n1 n1 n1 n0 n0 n0 n0 V))
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
