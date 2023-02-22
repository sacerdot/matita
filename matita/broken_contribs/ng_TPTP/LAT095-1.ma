include "logic/equality.ma".

(* Inclusion of: LAT095-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : LAT095-1 : TPTP v3.7.0. Released v2.6.0. *)

(*  Domain   : Lattice Theory (Weakly Associative Lattices) *)

(*  Problem  : Axiom for weakly associative lattices (WAL), part 4 *)

(*  Version  : [MP96] (equality) axioms : Especial. *)

(*  English  :  *)

(*  Refs     : [McC98] McCune (1998), Email to G. Sutcliffe *)

(*           : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq *)

(*  Source   : [TPTP] *)

(*  Names    :  *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.56 v3.4.0, 0.50 v3.3.0, 0.43 v3.1.0, 0.22 v2.7.0, 0.45 v2.6.0 *)

(*  Syntax   : Number of clauses     :    2 (   0 non-Horn;   2 unit;   1 RR) *)

(*             Number of atoms       :    2 (   2 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    4 (   2 constant; 0-2 arity) *)

(*             Number of variables   :    6 (   1 singleton) *)

(*             Maximal term depth    :   11 (   4 average) *)

(*  Comments : A UEQ part of LAT030-1 *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_wal_axioms_4:
 (∀Univ:Type.∀A:Univ.∀B:Univ.∀C:Univ.∀D:Univ.∀E:Univ.∀F:Univ.
∀a:Univ.
∀b:Univ.
∀join:∀_:Univ.∀_:Univ.Univ.
∀meet:∀_:Univ.∀_:Univ.Univ.
∀H0:∀A:Univ.∀B:Univ.∀C:Univ.∀D:Univ.∀E:Univ.∀F:Univ.eq Univ (join (meet (join (meet A B) (meet B (join A B))) C) (meet (join (meet A (join (join (meet B D) (meet E B)) B)) (meet (join (meet B (meet (meet (join B D) (join E B)) B)) (meet F (join B (meet (meet (join B D) (join E B)) B)))) (join A (join (join (meet B D) (meet E B)) B)))) (join (join (meet A B) (meet B (join A B))) C))) B.eq Univ (join b a) (join a b))
.
#Univ ##.
#A ##.
#B ##.
#C ##.
#D ##.
#E ##.
#F ##.
#a ##.
#b ##.
#join ##.
#meet ##.
#H0 ##.
nauto by H0 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)
