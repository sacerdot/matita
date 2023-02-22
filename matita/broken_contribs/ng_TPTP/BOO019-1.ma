include "logic/equality.ma".

(* Inclusion of: BOO019-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : BOO019-1 : TPTP v3.7.0. Released v1.2.0. *)

(*  Domain   : Boolean Algebra (Ternary) *)

(*  Problem  : Prove the independance of Ternary Boolean algebra axiom *)

(*  Version  : Especial. *)

(*  English  :  *)

(*  Refs     : [Win82] Winker (1982), Generation and Verification of Finite M *)

(*           : [BCP94] Bourely et al. (1994), A Method for Building Models Au *)

(*           : [Pel98] Peltier (1998), A New Method for Automated Finite Mode *)

(*  Source   : [BCP94] *)

(*  Names    : A1 [Win82] *)

(*           : Example 4 [BCP94] *)

(*           : 4.2.1 [Pel98] *)

(*  Status   : Satisfiable *)

(*  Rating   : 0.33 v3.2.0, 0.67 v3.1.0, 0.33 v2.4.0, 0.67 v2.2.1, 0.75 v2.2.0, 0.67 v2.1.0, 1.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :    5 (   0 non-Horn;   5 unit;   1 RR) *)

(*             Number of atoms       :    5 (   5 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    4 (   2 constant; 0-3 arity) *)

(*             Number of variables   :   11 (   1 singleton) *)

(*             Maximal term depth    :    3 (   2 average) *)

(*  Comments : Thought to be satisfiable. *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_ternary_multiply_1_independant:
 (∀Univ:Type.∀V:Univ.∀W:Univ.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀inverse:∀_:Univ.Univ.
∀multiply:∀_:Univ.∀_:Univ.∀_:Univ.Univ.
∀x:Univ.
∀y:Univ.
∀H0:∀X:Univ.∀Y:Univ.eq Univ (multiply X Y (inverse Y)) X.
∀H1:∀X:Univ.∀Y:Univ.eq Univ (multiply (inverse Y) Y X) X.
∀H2:∀X:Univ.∀Y:Univ.eq Univ (multiply X X Y) X.
∀H3:∀V:Univ.∀W:Univ.∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (multiply V W X) Y (multiply V W Z)) (multiply V W (multiply X Y Z)).eq Univ (multiply y x x) x)
.
#Univ ##.
#V ##.
#W ##.
#X ##.
#Y ##.
#Z ##.
#inverse ##.
#multiply ##.
#x ##.
#y ##.
#H0 ##.
#H1 ##.
#H2 ##.
#H3 ##.
nauto by H0,H1,H2,H3 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)
