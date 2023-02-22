include "logic/equality.ma".

(* Inclusion of: GRP181-4.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : GRP181-4 : TPTP v3.7.0. Bugfixed v1.2.1. *)

(*  Domain   : Group Theory (Lattice Ordered) *)

(*  Problem  : Distributivity of a lattice *)

(*  Version  : [Fuc94] (equality) axioms : Augmented. *)

(*  English  :  *)

(*  Refs     : [Fuc94] Fuchs (1994), The Application of Goal-Orientated Heuri *)

(*           : [Sch95] Schulz (1995), Explanation Based Learning for Distribu *)

(*  Source   : [Sch95] *)

(*  Names    : p12x [Sch95] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.33 v3.4.0, 0.25 v3.3.0, 0.43 v3.1.0, 0.44 v2.7.0, 0.36 v2.6.0, 0.00 v2.2.1, 0.56 v2.2.0, 0.57 v2.1.0, 1.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :   23 (   0 non-Horn;  23 unit;   4 RR) *)

(*             Number of atoms       :   23 (  23 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    8 (   4 constant; 0-2 arity) *)

(*             Number of variables   :   40 (   2 singleton) *)

(*             Maximal term depth    :    3 (   2 average) *)

(*  Comments : ORDERING LPO inverse > product > greatest_lower_bound > *)

(*             least_upper_bound > identity > a > b > c *)

(*           : ORDERING LPO greatest_lower_bound > least_upper_bound >  *)

(*             inverse > product > identity > a > b > c *)

(*  Bugfixes : v1.2.1 - Duplicate axioms in GRP004-2.ax removed. *)

(* -------------------------------------------------------------------------- *)

(* ----Include equality group theory axioms  *)

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

(* ----Include Lattice ordered group (equality) axioms *)

(* Inclusion of: Axioms/GRP004-2.ax *)

(* -------------------------------------------------------------------------- *)

(*  File     : GRP004-2 : TPTP v3.7.0. Bugfixed v1.2.0. *)

(*  Domain   : Group Theory (Lattice Ordered) *)

(*  Axioms   : Lattice ordered group (equality) axioms *)

(*  Version  : [Fuc94] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [Fuc94] Fuchs (1994), The Application of Goal-Orientated Heuri *)

(*           : [Sch95] Schulz (1995), Explanation Based Learning for Distribu *)

(*  Source   : [Sch95] *)

(*  Names    :  *)

(*  Status   :  *)

(*  Syntax   : Number of clauses    :   12 (   0 non-Horn;  12 unit;   0 RR) *)

(*             Number of atoms      :   12 (  12 equality) *)

(*             Maximal clause size  :    1 (   1 average) *)

(*             Number of predicates :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors   :    3 (   0 constant; 2-2 arity) *)

(*             Number of variables  :   28 (   2 singleton) *)

(*             Maximal term depth   :    3 (   2 average) *)

(*  Comments : Requires GRP004-0.ax *)

(* -------------------------------------------------------------------------- *)

(* ----Specification of the least upper bound and greatest lower bound *)

(* ----Monotony of multiply *)

(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_p12x:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀b:Univ.
∀c:Univ.
∀greatest_lower_bound:∀_:Univ.∀_:Univ.Univ.
∀identity:Univ.
∀inverse:∀_:Univ.Univ.
∀least_upper_bound:∀_:Univ.∀_:Univ.Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀H0:∀X:Univ.∀Y:Univ.eq Univ (inverse (least_upper_bound X Y)) (greatest_lower_bound (inverse X) (inverse Y)).
∀H1:∀X:Univ.∀Y:Univ.eq Univ (inverse (greatest_lower_bound X Y)) (least_upper_bound (inverse X) (inverse Y)).
∀H2:eq Univ (least_upper_bound a c) (least_upper_bound b c).
∀H3:eq Univ (greatest_lower_bound a c) (greatest_lower_bound b c).
∀H4:∀X:Univ.∀Y:Univ.eq Univ (inverse (multiply X Y)) (multiply (inverse Y) (inverse X)).
∀H5:∀X:Univ.eq Univ (inverse (inverse X)) X.
∀H6:eq Univ (inverse identity) identity.
∀H7:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (greatest_lower_bound Y Z) X) (greatest_lower_bound (multiply Y X) (multiply Z X)).
∀H8:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (least_upper_bound Y Z) X) (least_upper_bound (multiply Y X) (multiply Z X)).
∀H9:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply X (greatest_lower_bound Y Z)) (greatest_lower_bound (multiply X Y) (multiply X Z)).
∀H10:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply X (least_upper_bound Y Z)) (least_upper_bound (multiply X Y) (multiply X Z)).
∀H11:∀X:Univ.∀Y:Univ.eq Univ (greatest_lower_bound X (least_upper_bound X Y)) X.
∀H12:∀X:Univ.∀Y:Univ.eq Univ (least_upper_bound X (greatest_lower_bound X Y)) X.
∀H13:∀X:Univ.eq Univ (greatest_lower_bound X X) X.
∀H14:∀X:Univ.eq Univ (least_upper_bound X X) X.
∀H15:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (least_upper_bound X (least_upper_bound Y Z)) (least_upper_bound (least_upper_bound X Y) Z).
∀H16:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (greatest_lower_bound X (greatest_lower_bound Y Z)) (greatest_lower_bound (greatest_lower_bound X Y) Z).
∀H17:∀X:Univ.∀Y:Univ.eq Univ (least_upper_bound X Y) (least_upper_bound Y X).
∀H18:∀X:Univ.∀Y:Univ.eq Univ (greatest_lower_bound X Y) (greatest_lower_bound Y X).
∀H19:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (multiply X Y) Z) (multiply X (multiply Y Z)).
∀H20:∀X:Univ.eq Univ (multiply (inverse X) X) identity.
∀H21:∀X:Univ.eq Univ (multiply identity X) X.eq Univ a b)
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#a ##.
#b ##.
#c ##.
#greatest_lower_bound ##.
#identity ##.
#inverse ##.
#least_upper_bound ##.
#multiply ##.
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
#H20 ##.
#H21 ##.
nauto by H0,H1,H2,H3,H4,H5,H6,H7,H8,H9,H10,H11,H12,H13,H14,H15,H16,H17,H18,H19,H20,H21 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)
