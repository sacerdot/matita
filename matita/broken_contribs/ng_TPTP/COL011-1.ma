include "logic/equality.ma".

(* Inclusion of: COL011-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : COL011-1 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Combinatory Logic *)

(*  Problem  : Weak fixed point for O and Q1 *)

(*  Version  : [WM88] (equality) axioms. *)

(*  English  : The weak fixed point property holds for the set P consisting  *)

(*             of the combinators O and Q1, where (Ox)y = y(xy), ((Q1x)y)z  *)

(*             = x(zy). *)

(*  Refs     : [Smu85] Smullyan (1978), To Mock a Mocking Bird and Other Logi *)

(*           : [MW87]  McCune & Wos (1987), A Case Study in Automated Theorem *)

(*           : [WM88]  Wos & McCune (1988), Challenge Problems Focusing on Eq *)

(*           : [MW88]  McCune & Wos (1988), Some Fixed Point Problems in Comb *)

(*  Source   : [MW88] *)

(*  Names    : - [MW88] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.22 v3.4.0, 0.25 v3.3.0, 0.36 v3.1.0, 0.67 v2.7.0, 0.36 v2.6.0, 0.33 v2.5.0, 0.25 v2.4.0, 0.00 v2.2.1, 0.33 v2.2.0, 0.14 v2.1.0, 0.62 v2.0.0 *)

(*  Syntax   : Number of clauses     :    3 (   0 non-Horn;   3 unit;   1 RR) *)

(*             Number of atoms       :    3 (   3 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    4 (   3 constant; 0-2 arity) *)

(*             Number of variables   :    6 (   0 singleton) *)

(*             Maximal term depth    :    4 (   3 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_fixed_point:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀apply:∀_:Univ.∀_:Univ.Univ.
∀combinator:Univ.
∀o:Univ.
∀q1:Univ.
∀H0:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply q1 X) Y) Z) (apply X (apply Z Y)).
∀H1:∀X:Univ.∀Y:Univ.eq Univ (apply (apply o X) Y) (apply Y (apply X Y)).∃Y:Univ.eq Univ Y (apply combinator Y))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#apply ##.
#combinator ##.
#o ##.
#q1 ##.
#H0 ##.
#H1 ##.
napply (ex_intro ? ? ? ?) ##[
##2:
nauto by H0,H1 ##;
##| ##skip ##]
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)
