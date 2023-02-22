include "logic/equality.ma".

(* Inclusion of: GRP002-2.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : GRP002-2 : TPTP v3.7.0. Bugfixed v1.2.1. *)

(*  Domain   : Group Theory *)

(*  Problem  : Commutator equals identity in groups of order 3 *)

(*  Version  : [MOW76] (equality) axioms. *)

(*  English  : In a group, if (for all x) the cube of x is the identity  *)

(*             (i.e. a group of order 3), then the equation [[x,y],y]=  *)

(*             identity holds, where [x,y] is the product of x, y, the  *)

(*             inverse of x and the inverse of y (i.e. the commutator  *)

(*             of x and y). *)

(*  Refs     : [MOW76] McCharen et al. (1976), Problems and Experiments for a *)

(*  Source   : [ANL] *)

(*  Names    : commutator.ver2.in [ANL] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.11 v3.4.0, 0.12 v3.3.0, 0.00 v2.2.1, 0.22 v2.2.0, 0.29 v2.1.0, 0.29 v2.0.0 *)

(*  Syntax   : Number of clauses     :   12 (   0 non-Horn;  12 unit;   6 RR) *)

(*             Number of atoms       :   12 (  12 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :   10 (   8 constant; 0-2 arity) *)

(*             Number of variables   :    8 (   0 singleton) *)

(*             Maximal term depth    :    3 (   2 average) *)

(*  Comments :  *)

(*  Bugfixes : v1.2.1 - Clause x_cubed_is_identity fixed. *)

(* -------------------------------------------------------------------------- *)

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

(* ----Redundant two axioms, but established in standard axiomatizations. *)

(* ----This hypothesis is omitted in the ANL source version  *)
ntheorem prove_k_times_inverse_b_is_e:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀b:Univ.
∀c:Univ.
∀d:Univ.
∀h:Univ.
∀identity:Univ.
∀inverse:∀_:Univ.Univ.
∀j:Univ.
∀k:Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀H0:eq Univ (multiply j (inverse h)) k.
∀H1:eq Univ (multiply h b) j.
∀H2:eq Univ (multiply d (inverse b)) h.
∀H3:eq Univ (multiply c (inverse a)) d.
∀H4:eq Univ (multiply a b) c.
∀H5:∀X:Univ.eq Univ (multiply X (multiply X X)) identity.
∀H6:∀X:Univ.eq Univ (multiply X (inverse X)) identity.
∀H7:∀X:Univ.eq Univ (multiply X identity) X.
∀H8:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (multiply X Y) Z) (multiply X (multiply Y Z)).
∀H9:∀X:Univ.eq Univ (multiply (inverse X) X) identity.
∀H10:∀X:Univ.eq Univ (multiply identity X) X.eq Univ (multiply k (inverse b)) identity)
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#a ##.
#b ##.
#c ##.
#d ##.
#h ##.
#identity ##.
#inverse ##.
#j ##.
#k ##.
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
nauto by H0,H1,H2,H3,H4,H5,H6,H7,H8,H9,H10 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)
