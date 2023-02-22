set "baseuri" "cic:/matita/TPTP/ANA005-1".
include "logic/equality.ma".

(* Inclusion of: ANA005-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : ANA005-1 : TPTP v3.2.0. Released v1.0.0. *)

(*  Domain   : Analysis *)

(*  Problem  : The sum of two continuous functions is continuous *)

(*  Version  : [MOW76] axioms : Incomplete > Augmented > Complete. *)

(*  English  :  *)

(*  Refs     : [MOW76] McCharen et al. (1976), Problems and Experiments for a *)

(*  Source   : [ANL] *)

(*  Names    : BL3 [MOW76] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.71 v3.2.0, 0.86 v3.1.0, 0.78 v2.7.0, 0.83 v2.6.0, 0.86 v2.5.0, 0.60 v2.4.0, 1.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :   21 (   0 non-Horn;   7 unit;  16 RR) *)

(*             Number of atoms       :   42 (   5 equality) *)

(*             Maximal clause size   :    3 (   2 average) *)

(*             Number of predicates  :    2 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :   15 (   5 constant; 0-2 arity) *)

(*             Number of variables   :   35 (   0 singleton) *)

(*             Maximal term depth    :    6 (   2 average) *)

(*  Comments : No natural language descriptions are available. *)

(*           : Contributed to the ANL library by Woody Bledsoe. *)

(* -------------------------------------------------------------------------- *)

(* ----Include limits axioms  *)

(* Inclusion of: Axioms/ANA001-0.ax *)

(* -------------------------------------------------------------------------- *)

(*  File     : ANA001-0 : TPTP v3.2.0. Released v1.0.0. *)

(*  Domain   : Analysis (Limits) *)

(*  Axioms   : Analysis (limits) axioms for continuous functions *)

(*  Version  : [MOW76] axioms. *)

(*  English  :  *)

(*  Refs     : [MOW76] McCharen et al. (1976), Problems and Experiments for a *)

(*  Source   : [ANL] *)

(*  Names    :  *)

(*  Status   :  *)

(*  Syntax   : Number of clauses    :   14 (   0 non-Horn;   6 unit;   9 RR) *)

(*             Number of literals   :   27 (   5 equality) *)

(*             Maximal clause size  :    3 (   2 average) *)

(*             Number of predicates :    2 (   0 propositional; 2-2 arity) *)

(*             Number of functors   :    6 (   1 constant; 0-2 arity) *)

(*             Number of variables  :   27 (   0 singleton) *)

(*             Maximal term depth   :    3 (   1 average) *)

(*  Comments : No natural language descriptions are available. *)

(*           : "Contributed by W.W. Bledsoe in a private correspondence",  *)

(*             [MOW76]. *)

(* -------------------------------------------------------------------------- *)

(* ----Axiom 1  *)

(* ----Less than transitivity  *)

(* ----Axiom 2  *)

(* ----Axiom 3  *)

(* ----Axiom 4  *)

(* ----Axiom 5  *)

(* ----Axiom 6  *)

(* ----Axiom 7  *)

(* ----Axiom 8  *)

(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)

(* ----Clauses from the theorem  *)
theorem c_16:
 ∀Univ:Set.∀X:Univ.∀Xa:Univ.∀Y:Univ.∀Z:Univ.∀a:Univ.∀absolute:∀_:Univ.Univ.∀add:∀_:Univ.∀_:Univ.Univ.∀b:Univ.∀f:∀_:Univ.Univ.∀fp31:∀_:Univ.Univ.∀fp32:∀_:Univ.Univ.∀fp33:∀_:Univ.Univ.∀g:∀_:Univ.Univ.∀half:∀_:Univ.Univ.∀l1:Univ.∀l2:Univ.∀less_than:∀_:Univ.∀_:Univ.Prop.∀minimum:∀_:Univ.∀_:Univ.Univ.∀minus:∀_:Univ.Univ.∀n0:Univ.∀H0:∀X:Univ.∀_:less_than n0 X.less_than (absolute (add (fp33 X) (minus a))) X.∀H1:less_than n0 b.∀H2:∀X:Univ.∀Y:Univ.∀_:less_than (absolute (add Y (minus a))) (fp32 X).∀_:less_than n0 X.less_than (absolute (add (g Y) (minus l2))) X.∀H3:∀X:Univ.∀_:less_than n0 X.less_than n0 (fp32 X).∀H4:∀X:Univ.∀Y:Univ.∀_:less_than (absolute (add Y (minus a))) (fp31 X).∀_:less_than n0 X.less_than (absolute (add (f Y) (minus l1))) X.∀H5:∀X:Univ.∀_:less_than n0 X.less_than n0 (fp31 X).∀H6:∀X:Univ.∀Y:Univ.eq Univ (minus (add X Y)) (add (minus X) (minus Y)).∀H7:∀Xa:Univ.∀_:less_than n0 Xa.less_than n0 (half Xa).∀H8:∀Xa:Univ.∀_:less_than n0 Xa.less_than n0 (half Xa).∀H9:∀X:Univ.∀Y:Univ.eq Univ (add X Y) (add Y X).∀H10:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (add (add X Y) Z) (add X (add Y Z)).∀H11:∀X:Univ.∀Xa:Univ.∀Y:Univ.∀_:less_than (add (absolute X) (absolute Y)) Xa.less_than (absolute (add X Y)) Xa.∀H12:∀X:Univ.∀Xa:Univ.∀Y:Univ.∀_:less_than Y (half Xa).∀_:less_than X (half Xa).less_than (add X Y) Xa.∀H13:∀X:Univ.∀Y:Univ.∀_:less_than n0 Y.∀_:less_than n0 X.less_than (minimum X Y) Y.∀H14:∀X:Univ.∀Y:Univ.∀_:less_than n0 Y.∀_:less_than n0 X.less_than (minimum X Y) X.∀H15:∀X:Univ.∀Y:Univ.∀_:less_than n0 Y.∀_:less_than n0 X.less_than n0 (minimum X Y).∀H16:∀X:Univ.∀Y:Univ.∀Z:Univ.∀_:less_than Y Z.∀_:less_than X Y.less_than X Z.∀H17:∀X:Univ.less_than X X.∀H18:∀X:Univ.eq Univ (add n0 X) X.∀H19:∀X:Univ.eq Univ (add X n0) X.∃X:Univ.And (less_than (absolute (add (add (f (fp33 X)) (g (fp33 X))) (minus (add l1 l2)))) b) (less_than n0 X)
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
