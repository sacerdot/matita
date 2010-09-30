include "logic/equality.ma".

(* Inclusion of: COL047-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : COL047-1 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Combinatory Logic *)

(*  Problem  : Find a model for L and Q but not a strong fixed point *)

(*  Version  : [WM88] (equality) axioms. *)

(*  English  : The model one is seeking must satisfy L and Q and fail  *)

(*             to satisfy the strong fixed point property, where (Lx)y  *)

(*             = x(yy), ((Qx)y)z = y(xz). *)

(*  Refs     : [Zha92] Zhang (1992), Solution to an Open Question in Combinat *)

(*           : [Wos93] Wos (1993), The Kernel Strategy and Its Use for the St *)

(*           : [Pel98] Peltier (1998), A New Method for Automated Finite Mode *)

(*  Source   : [Zhang, 1992] *)

(*  Names    : Question 7 [Wos93] *)

(*           : Question 17 [Wos93] *)

(*           : 4.2.5 (CL2) [Pel98] *)

(*  Status   : Satisfiable *)

(*  Rating   : 0.33 v3.2.0, 0.67 v3.1.0, 0.33 v2.4.0, 0.67 v2.2.1, 0.75 v2.2.0, 0.67 v2.1.0, 1.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :    3 (   0 non-Horn;   3 unit;   1 RR) *)

(*             Number of atoms       :    3 (   3 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    4 (   2 constant; 0-2 arity) *)

(*             Number of variables   :    6 (   0 singleton) *)

(*             Maximal term depth    :    4 (   3 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_model:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀apply:∀_:Univ.∀_:Univ.Univ.
∀f:∀_:Univ.Univ.
∀l:Univ.
∀q:Univ.
∀H0:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply q X) Y) Z) (apply Y (apply X Z)).
∀H1:∀X:Univ.∀Y:Univ.eq Univ (apply (apply l X) Y) (apply X (apply Y Y)).∃Y:Univ.eq Univ (apply Y (f Y)) (apply (f Y) (apply Y (f Y))))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#apply ##.
#f ##.
#l ##.
#q ##.
#H0 ##.
#H1 ##.
napply (ex_intro ? ? ? ?) ##[
##2:
nauto by H0,H1 ##;
##| ##skip ##]
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)
