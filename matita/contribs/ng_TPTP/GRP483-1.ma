include "logic/equality.ma".

(* Inclusion of: GRP483-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : GRP483-1 : TPTP v3.7.0. Released v2.6.0. *)

(*  Domain   : Group Theory *)

(*  Problem  : Axiom for group theory, in double division and identity, part 3 *)

(*  Version  : [McC93] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [Neu86] Neumann (1986), Yet Another Single Law for Groups *)

(*           : [McC93] McCune (1993), Single Axioms for Groups and Abelian Gr *)

(*  Source   : [TPTP] *)

(*  Names    :  *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v3.4.0, 0.12 v3.3.0, 0.00 v2.6.0 *)

(*  Syntax   : Number of clauses     :    5 (   0 non-Horn;   5 unit;   1 RR) *)

(*             Number of atoms       :    5 (   5 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    7 (   4 constant; 0-2 arity) *)

(*             Number of variables   :    8 (   0 singleton) *)

(*             Maximal term depth    :    7 (   3 average) *)

(*  Comments : A UEQ part of GRP075-1 *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_these_axioms_3:
 (∀Univ:Type.∀A:Univ.∀B:Univ.∀C:Univ.∀D:Univ.
∀a3:Univ.
∀b3:Univ.
∀c3:Univ.
∀double_divide:∀_:Univ.∀_:Univ.Univ.
∀identity:Univ.
∀inverse:∀_:Univ.Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀H0:∀A:Univ.eq Univ identity (double_divide A (inverse A)).
∀H1:∀A:Univ.eq Univ (inverse A) (double_divide A identity).
∀H2:∀A:Univ.∀B:Univ.eq Univ (multiply A B) (double_divide (double_divide B A) identity).
∀H3:∀A:Univ.∀B:Univ.∀C:Univ.∀D:Univ.eq Univ (double_divide (double_divide (double_divide A (double_divide B identity)) (double_divide (double_divide C (double_divide D (double_divide D identity))) (double_divide A identity))) B) C.eq Univ (multiply (multiply a3 b3) c3) (multiply a3 (multiply b3 c3)))
.
#Univ ##.
#A ##.
#B ##.
#C ##.
#D ##.
#a3 ##.
#b3 ##.
#c3 ##.
#double_divide ##.
#identity ##.
#inverse ##.
#multiply ##.
#H0 ##.
#H1 ##.
#H2 ##.
#H3 ##.
nauto by H0,H1,H2,H3 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)