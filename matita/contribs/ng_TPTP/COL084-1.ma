include "logic/equality.ma".

(* Inclusion of: COL084-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : COL084-1 : TPTP v3.7.0. Released v2.6.0. *)

(*  Domain   : Combinatory Logic *)

(*  Problem  : Compatible Birds, part 2 *)

(*  Version  : Especial. *)

(*  English  :  *)

(*  Refs     : [Smu85] Smullyan (1978), To Mock a Mocking Bird and Other Logi *)

(*  Source   : [TPTP] *)

(*  Names    :  *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v2.6.0 *)

(*  Syntax   : Number of clauses     :    3 (   0 non-Horn;   3 unit;   1 RR) *)

(*             Number of atoms       :    3 (   3 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    4 (   2 constant; 0-2 arity) *)

(*             Number of variables   :    6 (   2 singleton) *)

(*             Maximal term depth    :    3 (   2 average) *)

(*  Comments : A UEQ part of COL054-1 *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_birds_are_compatible_2:
 (∀Univ:Type.∀A:Univ.∀B:Univ.∀C:Univ.
∀b:Univ.
∀compose:∀_:Univ.∀_:Univ.Univ.
∀mocking_bird:Univ.
∀response:∀_:Univ.∀_:Univ.Univ.
∀H0:∀A:Univ.∀B:Univ.∀C:Univ.eq Univ (response (compose A B) C) (response A (response B C)).
∀H1:∀A:Univ.eq Univ (response mocking_bird A) (response A A).∃A:Univ.∃B:Univ.eq Univ (response b B) A)
.
#Univ ##.
#A ##.
#B ##.
#C ##.
#b ##.
#compose ##.
#mocking_bird ##.
#response ##.
#H0 ##.
#H1 ##.
napply (ex_intro ? ? ? ?) ##[
##2:
napply (ex_intro ? ? ? ?) ##[
##2:
nauto by H0,H1 ##;
##| ##skip ##]
##| ##skip ##]
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)
