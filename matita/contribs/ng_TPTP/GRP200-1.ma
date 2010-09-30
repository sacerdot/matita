include "logic/equality.ma".

(* Inclusion of: GRP200-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : GRP200-1 : TPTP v3.7.0. Released v2.2.0. *)

(*  Domain   : Group Theory (Loops) *)

(*  Problem  : In Loops, Moufang-1 => Moufang-2. *)

(*  Version  : [MP96] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [McC98] McCune (1998), Email to G. Sutcliffe *)

(*           : [Wos96] Wos (1996), OTTER and the Moufang Identity Problem *)

(*           : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq *)

(*  Source   : [McC98] *)

(*  Names    : MFL-1 [MP96] *)

(*           : - [Wos96] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.22 v3.4.0, 0.25 v3.3.0, 0.29 v3.1.0, 0.33 v2.7.0, 0.27 v2.6.0, 0.00 v2.2.1 *)

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

(* ----Moufang-1: *)

(* ----Denial of Moufang-2: *)
ntheorem prove_moufang2:
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
∀H0:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (multiply X (multiply Y Z)) X) (multiply (multiply X Y) (multiply Z X)).
∀H1:∀X:Univ.eq Univ (multiply (left_inverse X) X) identity.
∀H2:∀X:Univ.eq Univ (multiply X (right_inverse X)) identity.
∀H3:∀X:Univ.∀Y:Univ.eq Univ (right_division (multiply X Y) Y) X.
∀H4:∀X:Univ.∀Y:Univ.eq Univ (multiply (right_division X Y) Y) X.
∀H5:∀X:Univ.∀Y:Univ.eq Univ (left_division X (multiply X Y)) Y.
∀H6:∀X:Univ.∀Y:Univ.eq Univ (multiply X (left_division X Y)) Y.
∀H7:∀X:Univ.eq Univ (multiply X identity) X.
∀H8:∀X:Univ.eq Univ (multiply identity X) X.eq Univ (multiply (multiply (multiply a b) c) b) (multiply a (multiply b (multiply c b))))
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
