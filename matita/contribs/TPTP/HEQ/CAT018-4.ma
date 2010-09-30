set "baseuri" "cic:/matita/TPTP/CAT018-4".
include "logic/equality.ma".

(* Inclusion of: CAT018-4.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : CAT018-4 : TPTP v3.2.0. Released v1.0.0. *)

(*  Domain   : Category Theory *)

(*  Problem  : If xy and yz exist, then so does x(yz) *)

(*  Version  : [Sco79] axioms : Reduced > Complete. *)

(*  English  :  *)

(*  Refs     : [Sco79] Scott (1979), Identity and Existence in Intuitionist L *)

(*  Source   : [TPTP] *)

(*  Names    :  *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.29 v3.1.0, 0.33 v2.7.0, 0.17 v2.6.0, 0.43 v2.5.0, 0.20 v2.4.0, 0.17 v2.2.1, 0.44 v2.2.0, 0.57 v2.1.0, 0.80 v2.0.0 *)

(*  Syntax   : Number of clauses     :   14 (   0 non-Horn;   6 unit;  11 RR) *)

(*             Number of atoms       :   24 (   7 equality) *)

(*             Maximal clause size   :    3 (   2 average) *)

(*             Number of predicates  :    3 (   0 propositional; 1-2 arity) *)

(*             Number of functors    :    6 (   3 constant; 0-2 arity) *)

(*             Number of variables   :   19 (   2 singleton) *)

(*             Maximal term depth    :    3 (   2 average) *)

(*  Comments : The dependent axioms have been removed. *)

(* -------------------------------------------------------------------------- *)

(* ----Include Scott's axioms for category theory  *)

(* Inclusion of: Axioms/CAT004-0.ax *)

(* -------------------------------------------------------------------------- *)

(*  File     : CAT004-0 : TPTP v3.2.0. Released v1.0.0. *)

(*  Domain   : Category Theory *)

(*  Axioms   : Category theory axioms *)

(*  Version  : [Sco79] axioms : Reduced > Complete. *)

(*  English  :  *)

(*  Refs     : [Sco79] Scott (1979), Identity and Existence in Intuitionist L *)

(*  Source   : [ANL] *)

(*  Names    :  *)

(*  Status   :  *)

(*  Syntax   : Number of clauses    :   11 (   0 non-Horn;   3 unit;   8 RR) *)

(*             Number of literals   :   21 (   7 equality) *)

(*             Maximal clause size  :    3 (   2 average) *)

(*             Number of predicates :    3 (   0 propositional; 1-2 arity) *)

(*             Number of functors   :    3 (   0 constant; 1-2 arity) *)

(*             Number of variables  :   19 (   2 singleton) *)

(*             Maximal term depth   :    3 (   2 average) *)

(*  Comments : The dependent axioms have been removed. *)

(* -------------------------------------------------------------------------- *)

(* ----Non-standard in that E(x) stands for "x exists", i.e. a system -for  *)

(* ----intuitionistic logic.  Viewed classically, this can be -taken  *)

(* ----as a partitioning of models M into elements of E and -other elements  *)

(* ----of M; then Scott's quantifiers are relativized -to range only over  *)

(* ----E, whereas free variables range over all of -M. *)

(* ----Quaife has this written: (this looks really weird, but results -from  *)

(* ----having = here stand for equivalence, and it is a strange -fact from  *)

(* ----Scott's conception that all non-existent things are -equivalent. all  *)

(* ----x all y ((x = y) | E(x) | E(y))).  *)

(* -----Restricted equality axioms  *)

(* -----Category theory axioms  *)

(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
theorem prove_a_bc_exists:
 ∀Univ:Set.∀X:Univ.∀Y:Univ.∀Z:Univ.∀a:Univ.∀b:Univ.∀c:Univ.∀codomain:∀_:Univ.Univ.∀compose:∀_:Univ.∀_:Univ.Univ.∀domain:∀_:Univ.Univ.∀equivalent:∀_:Univ.∀_:Univ.Prop.∀there_exists:∀_:Univ.Prop.∀H0:there_exists (compose b c).∀H1:there_exists (compose a b).∀H2:∀X:Univ.eq Univ (compose (codomain X) X) X.∀H3:∀X:Univ.eq Univ (compose X (domain X)) X.∀H4:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (compose X (compose Y Z)) (compose (compose X Y) Z).∀H5:∀X:Univ.∀Y:Univ.∀_:eq Univ (domain X) (codomain Y).∀_:there_exists (domain X).there_exists (compose X Y).∀H6:∀X:Univ.∀Y:Univ.∀_:there_exists (compose X Y).eq Univ (domain X) (codomain Y).∀H7:∀X:Univ.∀Y:Univ.∀_:there_exists (compose X Y).there_exists (domain X).∀H8:∀X:Univ.∀_:there_exists (codomain X).there_exists X.∀H9:∀X:Univ.∀_:there_exists (domain X).there_exists X.∀H10:∀X:Univ.∀Y:Univ.∀_:eq Univ X Y.∀_:there_exists X.equivalent X Y.∀H11:∀X:Univ.∀Y:Univ.∀_:equivalent X Y.eq Univ X Y.∀H12:∀X:Univ.∀Y:Univ.∀_:equivalent X Y.there_exists X.there_exists (compose a (compose b c))
.
intros.
autobatch depth=5 width=5 size=20 timeout=10;
try assumption.
print proofterm.
qed.

(* -------------------------------------------------------------------------- *)
