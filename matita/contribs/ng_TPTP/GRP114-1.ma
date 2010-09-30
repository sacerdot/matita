include "logic/equality.ma".

(* Inclusion of: GRP114-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : GRP114-1 : TPTP v3.7.0. Released v1.2.0. *)

(*  Domain   : Group Theory *)

(*  Problem  : Product of positive and negative parts of X equals X *)

(*  Version  : [MOW76] (equality) axioms : Augmented. *)

(*  English  : Prove that for each element X in a group, X is equal to the  *)

(*             product of its positive part (the union with the identity)  *)

(*             and its negative part (the intersection with the identity). *)

(*  Refs     : [Wos94] Wos (1994), Challenge in Group Theory *)

(*  Source   : [Wos94] *)

(*  Names    : - [Wos94] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.33 v3.4.0, 0.25 v3.3.0, 0.29 v3.1.0, 0.22 v2.7.0, 0.36 v2.6.0, 0.17 v2.5.0, 0.00 v2.4.0, 0.00 v2.2.1, 0.44 v2.2.0, 0.57 v2.1.0, 0.86 v2.0.0 *)

(*  Syntax   : Number of clauses     :   21 (   0 non-Horn;  21 unit;   2 RR) *)

(*             Number of atoms       :   21 (  21 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    8 (   2 constant; 0-2 arity) *)

(*             Number of variables   :   38 (   2 singleton) *)

(*             Maximal term depth    :    3 (   2 average) *)

(*  Comments : I know some of the axioms are redundant, and have put comments *)

(*             to that effect. However, I don't know how to make a complete *)

(*             standard axiomatisation for the union and intersection axioms. *)

(* -------------------------------------------------------------------------- *)

(* ----Include the axioms for named groups  *)

(* Inclusion of: Axioms/GRP004-0.ax *)

(* -------------------------------------------------------------------------- *)

(*  File     : GRP004-0 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Group Theory *)

(*  Axioms   : Group theory (equality) axioms *)

(*  Version  : [MOW76] (equality) axioms :  *)

(*             Reduced > Complete. *)

(*  English  :  *)

(*  Refs     : [MOW76] McCharen et al. (1976), Problems and Experiments for a *)

(*           : [Wos88] Wos (1988), Automated Reasoning - 33 Basic Research Pr *)

(*  Source   : [ANL] *)

(*  Names    :  *)

(*  Status   :  *)

(*  Syntax   : Number of clauses    :    3 (   0 non-Horn;   3 unit;   0 RR) *)

(*             Number of atoms      :    3 (   3 equality) *)

(*             Maximal clause size  :    1 (   1 average) *)

(*             Number of predicates :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors   :    3 (   1 constant; 0-2 arity) *)

(*             Number of variables  :    5 (   0 singleton) *)

(*             Maximal term depth   :    3 (   2 average) *)

(*  Comments : [MOW76] also contains redundant right_identity and *)

(*             right_inverse axioms. *)

(*           : These axioms are also used in [Wos88] p.186, also with *)

(*             right_identity and right_inverse. *)

(* -------------------------------------------------------------------------- *)

(* ----For any x and y in the group x*y is also in the group. No clause  *)

(* ----is needed here since this is an instance of reflexivity  *)

(* ----There exists an identity element  *)

(* ----For any x in the group, there exists an element y such that x*y = y*x  *)

(* ----= identity. *)

(* ----The operation '*' is associative  *)

(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)

(* ----This axiom is a lemma  *)

(* ----This axiom is a lemma  *)

(* ----This axiom is a lemma  *)
ntheorem prove_product:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀identity:Univ.
∀intersection:∀_:Univ.∀_:Univ.Univ.
∀inverse:∀_:Univ.Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀negative_part:∀_:Univ.Univ.
∀positive_part:∀_:Univ.Univ.
∀union:∀_:Univ.∀_:Univ.Univ.
∀H0:∀X:Univ.eq Univ (negative_part X) (intersection X identity).
∀H1:∀X:Univ.eq Univ (positive_part X) (union X identity).
∀H2:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (intersection Y Z) X) (intersection (multiply Y X) (multiply Z X)).
∀H3:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (union Y Z) X) (union (multiply Y X) (multiply Z X)).
∀H4:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply X (intersection Y Z)) (intersection (multiply X Y) (multiply X Z)).
∀H5:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply X (union Y Z)) (union (multiply X Y) (multiply X Z)).
∀H6:∀X:Univ.∀Y:Univ.eq Univ (intersection (union X Y) Y) Y.
∀H7:∀X:Univ.∀Y:Univ.eq Univ (union (intersection X Y) Y) Y.
∀H8:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (union X (union Y Z)) (union (union X Y) Z).
∀H9:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (intersection X (intersection Y Z)) (intersection (intersection X Y) Z).
∀H10:∀X:Univ.∀Y:Univ.eq Univ (union X Y) (union Y X).
∀H11:∀X:Univ.∀Y:Univ.eq Univ (intersection X Y) (intersection Y X).
∀H12:∀X:Univ.eq Univ (union X X) X.
∀H13:∀X:Univ.eq Univ (intersection X X) X.
∀H14:∀X:Univ.∀Y:Univ.eq Univ (inverse (multiply X Y)) (multiply (inverse Y) (inverse X)).
∀H15:∀X:Univ.eq Univ (inverse (inverse X)) X.
∀H16:eq Univ (inverse identity) identity.
∀H17:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (multiply X Y) Z) (multiply X (multiply Y Z)).
∀H18:∀X:Univ.eq Univ (multiply (inverse X) X) identity.
∀H19:∀X:Univ.eq Univ (multiply identity X) X.eq Univ (multiply (positive_part a) (negative_part a)) a)
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#a ##.
#identity ##.
#intersection ##.
#inverse ##.
#multiply ##.
#negative_part ##.
#positive_part ##.
#union ##.
#H0 ##.
#H1 ##.
#H2 ##.
#H3 ##.
#H4 ##.
#H5 ##.
#H6 ##.
#H7 ##.
#H8 ##.
#H9 ##.
#H10 ##.
#H11 ##.
#H12 ##.
#H13 ##.
#H14 ##.
#H15 ##.
#H16 ##.
#H17 ##.
#H18 ##.
#H19 ##.
nauto by H0,H1,H2,H3,H4,H5,H6,H7,H8,H9,H10,H11,H12,H13,H14,H15,H16,H17,H18,H19 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)
