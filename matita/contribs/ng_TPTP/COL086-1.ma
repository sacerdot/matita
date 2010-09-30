include "logic/equality.ma".

(* Inclusion of: COL086-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : COL086-1 : TPTP v3.7.0. Released v2.6.0. *)

(*  Domain   : Combinatory Logic *)

(*  Problem  : Happy Birds, part 2 *)

(*  Version  : Especial. *)

(*  English  :  *)

(*  Refs     : [Smu85] Smullyan (1978), To Mock a Mocking Bird and Other Logi *)

(*  Source   : [TPTP] *)

(*  Names    :  *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v2.6.0 *)

(*  Syntax   : Number of clauses     :    2 (   0 non-Horn;   2 unit;   2 RR) *)

(*             Number of atoms       :    2 (   2 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    3 (   2 constant; 0-2 arity) *)

(*             Number of variables   :    2 (   2 singleton) *)

(*             Maximal term depth    :    2 (   2 average) *)

(*  Comments : A UEQ part of COL055-1 *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_happiness_2:
 (∀Univ:Type.∀A:Univ.∀B:Univ.
∀a:Univ.
∀b:Univ.
∀response:∀_:Univ.∀_:Univ.Univ.
∀H0:eq Univ (response a b) b.∃A:Univ.∃B:Univ.eq Univ (response a B) A)
.
#Univ ##.
#A ##.
#B ##.
#a ##.
#b ##.
#response ##.
#H0 ##.
napply (ex_intro ? ? ? ?) ##[
##2:
napply (ex_intro ? ? ? ?) ##[
##2:
nauto by H0 ##;
##| ##skip ##]
##| ##skip ##]
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)
