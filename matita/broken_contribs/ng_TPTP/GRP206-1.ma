include "logic/equality.ma".

(* Inclusion of: GRP206-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : GRP206-1 : TPTP v3.7.0. Released v2.3.0. *)

(*  Domain   : Group Theory (Loops) *)

(*  Problem  : In Loops, Moufang-4 => Moufang-1. *)

(*  Version  : [MP96] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [Wos96] Wos (1996), OTTER and the Moufang Identity Problem *)

(*  Source   : [Wos96] *)

(*  Names    : - [Wos96] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.11 v3.4.0, 0.12 v3.3.0, 0.00 v2.3.0 *)

(*  Syntax   : Number of clauses     :   10 (   0 non-Horn;  10 unit;   1 RR) *)

(*             Number of atoms       :   10 (  10 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    9 (   4 constant; 0-2 arity) *)

(*             Number of variables   :   15 (   0 singleton) *)

(*             Maximal term depth    :    4 (   2 average) *)

(*  Comments : *)

(* -------------------------------------------------------------------------- *)

(* ----Loop axioms: *)

(* ----Moufang-4 *)

(* ----Denial of Moufang-1 *)
ntheorem prove_moufang1:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀b:Univ.
∀c:Univ.
∀identity:Univ.
∀left_division:∀_:Univ.∀_:Univ.Univ.
∀left_inverse:∀_:Univ.Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀right_division:∀_:Univ.∀_:Univ.Univ.
∀right_inverse:∀_:Univ.Univ.
∀H0:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply X (multiply (multiply Y Z) X)) (multiply (multiply X Y) (multiply Z X)).
∀H1:∀X:Univ.eq Univ (multiply (left_inverse X) X) identity.
∀H2:∀X:Univ.eq Univ (multiply X (right_inverse X)) identity.
∀H3:∀X:Univ.∀Y:Univ.eq Univ (right_division (multiply X Y) Y) X.
∀H4:∀X:Univ.∀Y:Univ.eq Univ (multiply (right_division X Y) Y) X.
∀H5:∀X:Univ.∀Y:Univ.eq Univ (left_division X (multiply X Y)) Y.
∀H6:∀X:Univ.∀Y:Univ.eq Univ (multiply X (left_division X Y)) Y.
∀H7:∀X:Univ.eq Univ (multiply X identity) X.
∀H8:∀X:Univ.eq Univ (multiply identity X) X.eq Univ (multiply (multiply a (multiply b c)) a) (multiply (multiply a b) (multiply c a)))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#a ##.
#b ##.
#c ##.
#identity ##.
#left_division ##.
#left_inverse ##.
#multiply ##.
#right_division ##.
#right_inverse ##.
#H0 ##.
#H1 ##.
#H2 ##.
#H3 ##.
#H4 ##.
#H5 ##.
#H6 ##.
#H7 ##.
#H8 ##.
nauto by H0,H1,H2,H3,H4,H5,H6,H7,H8 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)
