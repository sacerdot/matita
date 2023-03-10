set "baseuri" "cic:/matita/TPTP/LCL218-3".
include "logic/equality.ma".

(* Inclusion of: LCL218-3.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : LCL218-3 : TPTP v3.2.0. Released v2.3.0. *)

(*  Domain   : Logic Calculi (Propositional) *)

(*  Problem  : Principia Mathematica 2.67 *)

(*  Version  : [WR27] axioms. *)

(*  English  :  *)

(*  Refs     : [WR27]  Whitehead & Russell (1927), Principia Mathematica *)

(*  Source   : [WR27] *)

(*  Names    : Problem 2.67 [WR27] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.29 v3.2.0, 0.14 v3.1.0, 0.33 v2.6.0, 0.29 v2.5.0, 0.20 v2.4.0, 0.00 v2.3.0 *)

(*  Syntax   : Number of clauses     :    9 (   0 non-Horn;   7 unit;   3 RR) *)

(*             Number of atoms       :   12 (   1 equality) *)

(*             Maximal clause size   :    3 (   1 average) *)

(*             Number of predicates  :    3 (   0 propositional; 1-2 arity) *)

(*             Number of functors    :    5 (   2 constant; 0-2 arity) *)

(*             Number of variables   :   16 (   1 singleton) *)

(*             Maximal term depth    :    4 (   2 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)

(* ----Include axioms of propositional logic  *)

(* Inclusion of: Axioms/LCL004-0.ax *)

(* ------------------------------------------------------------------------------ *)

(*  File     : LCL004-0 : TPTP v3.2.0. Released v2.3.0. *)

(*  Domain   : Logic Calculi (Propositional) *)

(*  Axioms   : Propositional logic deduction axioms *)

(*  Version  : [WR27] axioms. *)

(*  English  :  *)

(*  Refs     : [WR27]  Whitehead & Russell (1927), Principia Mathematica *)

(*  Source   : [WR27] *)

(*  Names    :  *)

(*  Status   :  *)

(*  Syntax   : Number of clauses    :    8 (   0 non-Horn;   6 unit;   2 RR) *)

(*             Number of literals   :   11 (   1 equality) *)

(*             Maximal clause size  :    3 (   1 average) *)

(*             Number of predicates :    3 (   0 propositional; 1-2 arity) *)

(*             Number of functors   :    3 (   0 constant; 1-2 arity) *)

(*             Number of variables  :   16 (   1 singleton) *)

(*             Maximal term depth   :    4 (   2 average) *)

(*  Comments : This axiomatization follows [WR27], allowing full detachment *)

(*             but no chaining (which is a dependant theorem). Compare with *)

(*             LCL003-0.ax. *)

(* ------------------------------------------------------------------------------ *)

(*  input_clause(rule_3,axiom, *)

(*      [++theorem(implies(X,Z)), *)

(*       --theorem(implies(X,Y)), *)

(*       --theorem(implies(Y,Z))]). *)

(* ------------------------------------------------------------------------------ *)

(* -------------------------------------------------------------------------- *)
theorem prove_this:
 ???Univ:Set.???A:Univ.???B:Univ.???C:Univ.???X:Univ.???Y:Univ.???axiomP:???_:Univ.Prop.???implies:???_:Univ.???_:Univ.Univ.???not:???_:Univ.Univ.???or:???_:Univ.???_:Univ.Univ.???p:Univ.???q:Univ.???theoremP:???_:Univ.Prop.???H0:???X:Univ.???Y:Univ.???_:theoremP Y.???_:theoremP (implies Y X).theoremP X.???H1:???X:Univ.???_:axiomP X.theoremP X.???H2:???X:Univ.???Y:Univ.eq Univ (implies X Y) (or (not X) Y).???H3:???A:Univ.???B:Univ.???C:Univ.axiomP (implies (implies A B) (implies (or C A) (or C B))).???H4:???A:Univ.???B:Univ.???C:Univ.axiomP (implies (or A (or B C)) (or B (or A C))).???H5:???A:Univ.???B:Univ.axiomP (implies (or A B) (or B A)).???H6:???A:Univ.???B:Univ.axiomP (implies A (or B A)).???H7:???A:Univ.axiomP (implies (or A A) A).theoremP (implies (implies (or p q) q) (implies p q))
.
intros.
autobatch depth=5 width=5 size=20 timeout=10;
try assumption.
print proofterm.
qed.

(* -------------------------------------------------------------------------- *)
