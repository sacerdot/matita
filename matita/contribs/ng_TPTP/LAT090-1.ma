include "logic/equality.ma".

(* Inclusion of: LAT090-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : LAT090-1 : TPTP v3.7.0. Released v2.6.0. *)

(*  Domain   : Lattice Theory (Weakly Associative Lattices) *)

(*  Problem  : Absorption basis for WAL, part 3 *)

(*  Version  : [MP96] (equality) axioms : Especial. *)

(*  English  :  *)

(*  Refs     : [McC98] McCune (1998), Email to G. Sutcliffe *)

(*           : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq *)

(*  Source   : [TPTP] *)

(*  Names    :  *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v2.6.0 *)

(*  Syntax   : Number of clauses     :    6 (   0 non-Horn;   6 unit;   1 RR) *)

(*             Number of atoms       :    6 (   6 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    3 (   1 constant; 0-2 arity) *)

(*             Number of variables   :   12 (   5 singleton) *)

(*             Maximal term depth    :    4 (   2 average) *)

(*  Comments : A UEQ part of LAT029-1 *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_normal_axioms_3:
 (∀Univ:Type.∀A:Univ.∀B:Univ.∀C:Univ.
∀a:Univ.
∀join:∀_:Univ.∀_:Univ.Univ.
∀meet:∀_:Univ.∀_:Univ.Univ.
∀H0:∀A:Univ.∀B:Univ.∀C:Univ.eq Univ (join (join (meet A B) (meet C A)) A) A.
∀H1:∀A:Univ.∀B:Univ.∀C:Univ.eq Univ (meet (meet (join A B) (join C A)) A) A.
∀H2:∀A:Univ.∀B:Univ.eq Univ (join (meet A B) (meet B (join A B))) B.
∀H3:∀A:Univ.∀B:Univ.eq Univ (join (meet A A) (meet B (join A A))) A.
∀H4:∀A:Univ.∀B:Univ.eq Univ (join (meet A B) (meet A (join A B))) A.eq Univ (join a a) a)
.
#Univ ##.
#A ##.
#B ##.
#C ##.
#a ##.
#join ##.
#meet ##.
#H0 ##.
#H1 ##.
#H2 ##.
#H3 ##.
#H4 ##.
nauto by H0,H1,H2,H3,H4 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)
