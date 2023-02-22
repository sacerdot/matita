include "logic/equality.ma".

(* Inclusion of: GRP024-5.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : GRP024-5 : TPTP v3.7.0. Released v2.2.0. *)

(*  Domain   : Group Theory *)

(*  Problem  : Levi commutator problem. *)

(*  Version  : [McC98] (equality) axioms. *)

(*  English  : In group theory, if the commutator [x,y] is associative, *)

(*             then x*[y,z] = [y,z]*x. *)

(*  Refs     : [McC98] McCune (1998), Email to G. Sutcliffe *)

(*           : [ML92]  McCune & Lusk (1992), A Challenging Theorem of Levi *)

(*           : [Kur56] Kurosh (1956), The Theory of Groups *)

(*  Source   : [McC98] *)

(*  Names    : *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.33 v3.4.0, 0.38 v3.3.0, 0.57 v3.2.0, 0.50 v3.1.0, 0.44 v2.7.0, 0.64 v2.6.0, 0.33 v2.5.0, 0.00 v2.4.0, 0.33 v2.3.0, 0.67 v2.2.1 *)

(*  Syntax   : Number of clauses     :    6 (   0 non-Horn;   6 unit;   1 RR) *)

(*             Number of atoms       :    6 (   6 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    7 (   4 constant; 0-2 arity) *)

(*             Number of variables   :   10 (   0 singleton) *)

(*             Maximal term depth    :    4 (   3 average) *)

(*  Comments : *)

(* -------------------------------------------------------------------------- *)

(* ----Include group theory axioms *)

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

(* ----Definition of commutator: *)

(* ----Theorem: commutator is associative implies x*[y,z] = [y,z]*x. *)

(* ----Hypothesis: *)

(* ----Denial of conclusion: *)
ntheorem prove_center:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀b:Univ.
∀c:Univ.
∀commutator:∀_:Univ.∀_:Univ.Univ.
∀identity:Univ.
∀inverse:∀_:Univ.Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀H0:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (commutator (commutator X Y) Z) (commutator X (commutator Y Z)).
∀H1:∀X:Univ.∀Y:Univ.eq Univ (commutator X Y) (multiply (inverse X) (multiply (inverse Y) (multiply X Y))).
∀H2:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (multiply X Y) Z) (multiply X (multiply Y Z)).
∀H3:∀X:Univ.eq Univ (multiply (inverse X) X) identity.
∀H4:∀X:Univ.eq Univ (multiply identity X) X.eq Univ (multiply a (commutator b c)) (multiply (commutator b c) a))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#a ##.
#b ##.
#c ##.
#commutator ##.
#identity ##.
#inverse ##.
#multiply ##.
#H0 ##.
#H1 ##.
#H2 ##.
#H3 ##.
#H4 ##.
nauto by H0,H1,H2,H3,H4 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)
