include "logic/equality.ma".

(* Inclusion of: COL075-2.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : COL075-2 : TPTP v3.7.0. Released v1.2.0. *)

(*  Domain   : Combinatory Logic *)

(*  Problem  : Lemma 1 for showing the unsatisfiable variant of TRC *)

(*  Version  : [Jec95] (equality) axioms : Reduced > Incomplete. *)

(*  English  : Searching for a diagonal combinator F with the property  *)

(*             f X Y = X X. *)

(*  Refs     : [Jec95] Jech (1995), Otter Experiments in a System of Combinat *)

(*  Source   : [Jec95] *)

(*  Names    : - [Jec95] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.11 v3.4.0, 0.12 v3.3.0, 0.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :    3 (   0 non-Horn;   3 unit;   1 RR) *)

(*             Number of atoms       :    3 (   3 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    5 (   2 constant; 0-2 arity) *)

(*             Number of variables   :    6 (   1 singleton) *)

(*             Maximal term depth    :    4 (   3 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)

(* ----Don't include axioms of Type-respecting combinators  *)

(* include('Axioms/COL001-0.ax'). *)

(* -------------------------------------------------------------------------- *)

(* ----Replace k function by k combinator  *)

(* input_clause(k_definition,axiom, *)

(*     [++equal(apply(k(X),Y),X)]). *)

(* ----Replace k function by k combinator  *)

(* input_clause(abstraction,axiom, *)

(*     [++equal(apply(apply(apply(abstraction,X),Y),Z),apply(apply(X,k(Z)), *)

(* apply(Y,Z)))]). *)

(* ----Subsitution axioms  *)
ntheorem prove_diagonal_combinator:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀abstraction:Univ.
∀apply:∀_:Univ.∀_:Univ.Univ.
∀b:∀_:Univ.Univ.
∀c:∀_:Univ.Univ.
∀k:Univ.
∀H0:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply abstraction X) Y) Z) (apply (apply X (apply k Z)) (apply Y Z)).
∀H1:∀X:Univ.∀Y:Univ.eq Univ (apply (apply k X) Y) X.∃Y:Univ.eq Univ (apply (apply Y (b Y)) (c Y)) (apply (b Y) (b Y)))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#abstraction ##.
#apply ##.
#b ##.
#c ##.
#k ##.
#H0 ##.
#H1 ##.
napply (ex_intro ? ? ? ?) ##[
##2:
nauto by H0,H1 ##;
##| ##skip ##]
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)
