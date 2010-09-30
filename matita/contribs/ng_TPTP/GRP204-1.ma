include "logic/equality.ma".

(* Inclusion of: GRP204-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : GRP204-1 : TPTP v3.7.0. Released v2.2.0. *)

(*  Domain   : Group Theory (Loops) *)

(*  Problem  : A non-basis for Moufang loops. *)

(*  Version  : [MP96] (equality) axioms : Especial. *)

(*  English  : Left identity, left inverse, Moufang-1 do not imply Moufang-2; *)

(*             that is, is not a basis for Moufang loops. *)

(*  Refs     : [McC98] McCune (1998), Email to G. Sutcliffe *)

(*           : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq *)

(*  Source   : [McC98] *)

(*  Names    : MFL-8 [MP96] *)

(*  Status   : Satisfiable *)

(*  Rating   : 0.33 v3.2.0, 0.67 v3.1.0, 0.33 v2.4.0, 0.67 v2.3.0, 1.00 v2.2.1 *)

(*  Syntax   : Number of clauses     :    4 (   0 non-Horn;   4 unit;   1 RR) *)

(*             Number of atoms       :    4 (   4 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    6 (   4 constant; 0-2 arity) *)

(*             Number of variables   :    5 (   0 singleton) *)

(*             Maximal term depth    :    4 (   3 average) *)

(*  Comments : The smallest model has 3 elements. *)

(* -------------------------------------------------------------------------- *)

(* ----Left identity and left inverse: *)

(* ----Moufang-1: *)

(* ----Denial of Moufang-2: *)
ntheorem prove_moufang2:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀b:Univ.
∀c:Univ.
∀identity:Univ.
∀left_inverse:∀_:Univ.Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀H0:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (multiply X (multiply Y Z)) X) (multiply (multiply X Y) (multiply Z X)).
∀H1:∀X:Univ.eq Univ (multiply (left_inverse X) X) identity.
∀H2:∀X:Univ.eq Univ (multiply identity X) X.eq Univ (multiply (multiply (multiply a b) c) b) (multiply a (multiply b (multiply c b))))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#a ##.
#b ##.
#c ##.
#identity ##.
#left_inverse ##.
#multiply ##.
#H0 ##.
#H1 ##.
#H2 ##.
nauto by H0,H1,H2 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)
