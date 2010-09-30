include "logic/equality.ma".

(* Inclusion of: LAT087-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : LAT087-1 : TPTP v3.7.0. Released v2.6.0. *)

(*  Domain   : Lattice Theory *)

(*  Problem  : Axiom for lattice theory, part 8 *)

(*  Version  : [MP96] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [McC98] McCune (1998), Email to G. Sutcliffe *)

(*           : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq *)

(*  Source   : [TPTP] *)

(*  Names    :  *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.67 v3.4.0, 0.62 v3.3.0, 0.43 v3.1.0, 0.22 v2.7.0, 0.55 v2.6.0 *)

(*  Syntax   : Number of clauses     :    2 (   0 non-Horn;   2 unit;   1 RR) *)

(*             Number of atoms       :    2 (   2 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    4 (   2 constant; 0-2 arity) *)

(*             Number of variables   :    7 (   1 singleton) *)

(*             Maximal term depth    :   12 (   4 average) *)

(*  Comments : A UEQ part of LAT015-1 *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_normal_axioms_8:
 (∀Univ:Type.∀A:Univ.∀B:Univ.∀C:Univ.∀D:Univ.∀E:Univ.∀F:Univ.∀G:Univ.
∀a:Univ.
∀b:Univ.
∀join:∀_:Univ.∀_:Univ.Univ.
∀meet:∀_:Univ.∀_:Univ.Univ.
∀H0:∀A:Univ.∀B:Univ.∀C:Univ.∀D:Univ.∀E:Univ.∀F:Univ.∀G:Univ.eq Univ (join (meet (join (meet A B) (meet B (join A B))) C) (meet (join (meet A (join (join (meet D B) (meet B E)) B)) (meet (join (meet B (meet (meet (join D (join B E)) (join F B)) B)) (meet G (join B (meet (meet (join D (join B E)) (join F B)) B)))) (join A (join (join (meet D B) (meet B E)) B)))) (join (join (meet A B) (meet B (join A B))) C))) B.eq Univ (join a (meet a b)) a)
.
#Univ ##.
#A ##.
#B ##.
#C ##.
#D ##.
#E ##.
#F ##.
#G ##.
#a ##.
#b ##.
#join ##.
#meet ##.
#H0 ##.
nauto by H0 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)
