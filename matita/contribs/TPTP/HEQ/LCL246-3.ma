set "baseuri" "cic:/matita/TPTP/LCL246-3".
include "logic/equality.ma".

(* Inclusion of: LCL246-3.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : LCL246-3 : TPTP v3.2.0. Released v2.3.0. *)

(*  Domain   : Logic Calculi (Propositional) *)

(*  Problem  : Principia Mathematica 3.35 *)

(*  Version  : [WR27] axioms. *)

(*  English  :  *)

(*  Refs     : [WR27]  Whitehead & Russell (1927), Principia Mathematica *)

(*  Source   : [WR27] *)

(*  Names    : Problem 3.35 [WR27] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.57 v3.2.0, 0.29 v3.1.0, 0.44 v2.7.0, 0.33 v2.6.0, 0.43 v2.5.0, 0.20 v2.4.0, 0.00 v2.3.0 *)

(*  Syntax   : Number of clauses     :   10 (   0 non-Horn;   8 unit;   3 RR) *)

(*             Number of atoms       :   13 (   2 equality) *)

(*             Maximal clause size   :    3 (   1 average) *)

(*             Number of predicates  :    3 (   0 propositional; 1-2 arity) *)

(*             Number of functors    :    6 (   2 constant; 0-2 arity) *)

(*             Number of variables   :   18 (   1 singleton) *)

(*             Maximal term depth    :    4 (   3 average) *)

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

(* Inclusion of: Axioms/LCL004-1.ax *)

(* -------------------------------------------------------------------------- *)

(*  File     : LCL004-1 : TPTP v3.2.0. Released v2.3.0. *)

(*  Domain   : Logic Calculi (Propositional) *)

(*  Axioms   : Propositional logic deduction axioms for AND *)

(*  Version  : [WR27] axioms. *)

(*  English  :  *)

(*  Refs     : [WR27]  Whitehead & Russell (1927), Principia Mathematica *)

(*  Source   : [WR27] *)

(*  Names    :  *)

(*  Status   :  *)

(*  Syntax   : Number of clauses    :    1 (   0 non-Horn;   1 unit;   0 RR) *)

(*             Number of literals   :    1 (   1 equality) *)

(*             Maximal clause size  :    1 (   1 average) *)

(*             Number of predicates :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors   :    3 (   0 constant; 1-2 arity) *)

(*             Number of variables  :    2 (   0 singleton) *)

(*             Maximal term depth   :    4 (   3 average) *)

(*  Comments : Requires LCL004-0.ax *)

(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
theorem prove_this:
 ∀Univ:Set.∀A:Univ.∀B:Univ.∀C:Univ.∀P:Univ.∀Q:Univ.∀X:Univ.∀Y:Univ.∀myand:∀_:Univ.∀_:Univ.Univ.∀axiomP:∀_:Univ.Prop.∀implies:∀_:Univ.∀_:Univ.Univ.∀not:∀_:Univ.Univ.∀or:∀_:Univ.∀_:Univ.Univ.∀p:Univ.∀q:Univ.∀theoremP:∀_:Univ.Prop.∀H0:∀P:Univ.∀Q:Univ.eq Univ (myand P Q) (not (or (not P) (not Q))).∀H1:∀X:Univ.∀Y:Univ.∀_:theoremP Y.∀_:theoremP (implies Y X).theoremP X.∀H2:∀X:Univ.∀_:axiomP X.theoremP X.∀H3:∀X:Univ.∀Y:Univ.eq Univ (implies X Y) (or (not X) Y).∀H4:∀A:Univ.∀B:Univ.∀C:Univ.axiomP (implies (implies A B) (implies (or C A) (or C B))).∀H5:∀A:Univ.∀B:Univ.∀C:Univ.axiomP (implies (or A (or B C)) (or B (or A C))).∀H6:∀A:Univ.∀B:Univ.axiomP (implies (or A B) (or B A)).∀H7:∀A:Univ.∀B:Univ.axiomP (implies A (or B A)).∀H8:∀A:Univ.axiomP (implies (or A A) A).theoremP (implies (myand p (implies p q)) q)
.
intros.
autobatch depth=5 width=5 size=20 timeout=10;
try assumption.
print proofterm.
qed.

(* -------------------------------------------------------------------------- *)
