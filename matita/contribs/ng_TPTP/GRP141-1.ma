include "logic/equality.ma".

(* Inclusion of: GRP141-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : GRP141-1 : TPTP v3.7.0. Bugfixed v1.2.1. *)

(*  Domain   : Group Theory (Lattice Ordered) *)

(*  Problem  : Prove greatest lower-bound axiom using a transformation *)

(*  Version  : [Fuc94] (equality) axioms. *)

(*  English  : This problem proves the original greatest lower-bound axiom *)

(*             from the equational axiomatization. *)

(*  Refs     : [Fuc94] Fuchs (1994), The Application of Goal-Orientated Heuri *)

(*           : [Sch95] Schulz (1995), Explanation Based Learning for Distribu *)

(*  Source   : [Sch95] *)

(*  Names    : ax_glb1d [Sch95]  *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v3.4.0, 0.12 v3.3.0, 0.00 v2.2.1, 0.22 v2.2.0, 0.29 v2.1.0, 0.14 v2.0.0 *)

(*  Syntax   : Number of clauses     :   18 (   0 non-Horn;  18 unit;   3 RR) *)

(*             Number of atoms       :   18 (  18 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    8 (   4 constant; 0-2 arity) *)

(*             Number of variables   :   33 (   2 singleton) *)

(*             Maximal term depth    :    3 (   2 average) *)

(*  Comments : ORDERING LPO inverse > product > greatest_lower_bound >  *)

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
ntheorem prove_ax_glb1d:
 (???Univ:Type.???X:Univ.???Y:Univ.???Z:Univ.
???a:Univ.
???b:Univ.
???c:Univ.
???greatest_lower_bound:???_:Univ.???_:Univ.Univ.
???identity:Univ.
???inverse:???_:Univ.Univ.
???least_upper_bound:???_:Univ.???_:Univ.Univ.
???multiply:???_:Univ.???_:Univ.Univ.
???H0:eq Univ (least_upper_bound b c) b.
???H1:eq Univ (least_upper_bound a c) a.
???H2:???X:Univ.???Y:Univ.???Z:Univ.eq Univ (multiply (greatest_lower_bound Y Z) X) (greatest_lower_bound (multiply Y X) (multiply Z X)).
???H3:???X:Univ.???Y:Univ.???Z:Univ.eq Univ (multiply (least_upper_bound Y Z) X) (least_upper_bound (multiply Y X) (multiply Z X)).
???H4:???X:Univ.???Y:Univ.???Z:Univ.eq Univ (multiply X (greatest_lower_bound Y Z)) (greatest_lower_bound (multiply X Y) (multiply X Z)).
???H5:???X:Univ.???Y:Univ.???Z:Univ.eq Univ (multiply X (least_upper_bound Y Z)) (least_upper_bound (multiply X Y) (multiply X Z)).
???H6:???X:Univ.???Y:Univ.eq Univ (greatest_lower_bound X (least_upper_bound X Y)) X.
???H7:???X:Univ.???Y:Univ.eq Univ (least_upper_bound X (greatest_lower_bound X Y)) X.
???H8:???X:Univ.eq Univ (greatest_lower_bound X X) X.
???H9:???X:Univ.eq Univ (least_upper_bound X X) X.
???H10:???X:Univ.???Y:Univ.???Z:Univ.eq Univ (least_upper_bound X (least_upper_bound Y Z)) (least_upper_bound (least_upper_bound X Y) Z).
???H11:???X:Univ.???Y:Univ.???Z:Univ.eq Univ (greatest_lower_bound X (greatest_lower_bound Y Z)) (greatest_lower_bound (greatest_lower_bound X Y) Z).
???H12:???X:Univ.???Y:Univ.eq Univ (least_upper_bound X Y) (least_upper_bound Y X).
???H13:???X:Univ.???Y:Univ.eq Univ (greatest_lower_bound X Y) (greatest_lower_bound Y X).
???H14:???X:Univ.???Y:Univ.???Z:Univ.eq Univ (multiply (multiply X Y) Z) (multiply X (multiply Y Z)).
???H15:???X:Univ.eq Univ (multiply (inverse X) X) identity.
???H16:???X:Univ.eq Univ (multiply identity X) X.eq Univ (greatest_lower_bound (greatest_lower_bound a b) c) c)
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
nauto by H0,H1,H2,H3,H4,H5,H6,H7,H8,H9,H10,H11,H12,H13,H14,H15,H16 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)
