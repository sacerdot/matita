include "logic/equality.ma".

(* Inclusion of: LAT077-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : LAT077-1 : TPTP v3.7.0. Released v2.6.0. *)

(*  Domain   : Lattice Theory (Ortholattices) *)

(*  Problem  : Given single axiom MOL-27B1, prove modularity *)

(*  Version  : [MRV03] (equality) axioms. *)

(*  English  : Given a single axiom candidate MOL-27B1 for modular ortholattices *)

(*             (MOL) in terms of the Sheffer Stroke, prove a Sheffer stroke form  *)

(*             of modularity. *)

(*  Refs     : [MRV03] McCune et al. (2003), Sheffer Stroke Bases for Ortholatt *)

(*  Source   : [MRV03] *)

(*  Names    : MOL-27B1-modularity [MRV03] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 1.00 v2.6.0 *)

(*  Syntax   : Number of clauses     :    2 (   0 non-Horn;   2 unit;   1 RR) *)

(*             Number of atoms       :    2 (   2 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    4 (   3 constant; 0-2 arity) *)

(*             Number of variables   :    4 (   1 singleton) *)

(*             Maximal term depth    :    9 (   5 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)

(* ----Single axiom MOL-27B1 *)

(* ----Denial of Sheffer stroke modularity *)
ntheorem modularity:
 (∀Univ:Type.∀A:Univ.∀B:Univ.∀C:Univ.∀D:Univ.
∀a:Univ.
∀b:Univ.
∀c:Univ.
∀f:∀_:Univ.∀_:Univ.Univ.
∀H0:∀A:Univ.∀B:Univ.∀C:Univ.∀D:Univ.eq Univ (f (f (f (f B A) (f C A)) D) (f A (f (f (f (f (f (f B B) A) C) C) A) B))) A.eq Univ (f a (f b (f a (f c c)))) (f a (f c (f a (f b b)))))
.
#Univ ##.
#A ##.
#B ##.
#C ##.
#D ##.
#a ##.
#b ##.
#c ##.
#f ##.
#H0 ##.
nauto by H0 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)
