include "logic/equality.ma".

(* Inclusion of: GRP001-4.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : GRP001-4 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Group Theory *)

(*  Problem  : X^2 = identity => commutativity *)

(*  Version  : [Wos65] (equality) axioms : Incomplete. *)

(*  English  : If the square of every element is the identity, the system  *)

(*             is commutative. *)

(*  Refs     : [Wos65] Wos (1965), Unpublished Note *)

(*           : [Pel86] Pelletier (1986), Seventy-five Problems for Testing Au *)

(*  Source   : [Pel86] *)

(*  Names    : Pelletier 65 [Pel86] *)

(*           : x2_quant.in [OTTER] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v2.2.1, 0.22 v2.2.0, 0.29 v2.1.0, 0.25 v2.0.0 *)

(*  Syntax   : Number of clauses     :    5 (   0 non-Horn;   5 unit;   2 RR) *)

(*             Number of atoms       :    5 (   5 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    5 (   4 constant; 0-2 arity) *)

(*             Number of variables   :    5 (   0 singleton) *)

(*             Maximal term depth    :    3 (   2 average) *)

(*  Comments : [Pel86] says "... problems, published I think, by Larry Wos  *)

(*             (but I cannot locate where)." *)

(* -------------------------------------------------------------------------- *)

(* ----The operation '*' is associative  *)

(* ----There exists an identity element 'e' defined below. *)
ntheorem prove_b_times_a_is_c:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀b:Univ.
∀c:Univ.
∀identity:Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀H0:eq Univ (multiply a b) c.
∀H1:∀X:Univ.eq Univ (multiply X X) identity.
∀H2:∀X:Univ.eq Univ (multiply identity X) X.
∀H3:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (multiply X Y) Z) (multiply X (multiply Y Z)).eq Univ (multiply b a) c)
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#a ##.
#b ##.
#c ##.
#identity ##.
#multiply ##.
#H0 ##.
#H1 ##.
#H2 ##.
#H3 ##.
nauto by H0,H1,H2,H3 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)
