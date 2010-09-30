include "logic/equality.ma".

(* Inclusion of: GRP203-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : GRP203-1 : TPTP v3.7.0. Released v2.2.0. *)

(*  Domain   : Group Theory (Loops) *)

(*  Problem  : Left identity, left inverse, Moufang-3 => Moufang-2 *)

(*  Version  : [MP96] (equality) axioms : Especial. *)

(*  English  :  *)

(*  Refs     : [McC98] McCune (1998), Email to G. Sutcliffe *)

(*           : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq *)

(*  Source   : [McC98] *)

(*  Names    : MFL-7 [MP96] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.11 v3.4.0, 0.12 v3.3.0, 0.14 v3.2.0, 0.21 v3.1.0, 0.11 v2.7.0, 0.18 v2.6.0, 0.00 v2.2.1 *)

(*  Syntax   : Number of clauses     :    4 (   0 non-Horn;   4 unit;   1 RR) *)

(*             Number of atoms       :    4 (   4 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    6 (   4 constant; 0-2 arity) *)

(*             Number of variables   :    5 (   0 singleton) *)

(*             Maximal term depth    :    4 (   3 average) *)

(*  Comments : Given left identity and left inverse, Moufang-2 and Moufang-3 *)

(*             are equivalent, but Moufang-1 is weaker (see MFL-8). *)

(* -------------------------------------------------------------------------- *)

(* ----Left identity and left inverse: *)

(* ----Moufang-3: *)

(* ----Denial of Moufang-2: *)
ntheorem prove_moufang2:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀b:Univ.
∀c:Univ.
∀identity:Univ.
∀left_inverse:∀_:Univ.Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀H0:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (multiply (multiply X Y) X) Z) (multiply X (multiply Y (multiply X Z))).
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
