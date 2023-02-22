include "logic/equality.ma".

(* Inclusion of: COL053-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : COL053-1 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Combinatory Logic *)

(*  Problem  : An Exercise in Composition *)

(*  Version  : Especial. *)

(*  English  : For all birds x and y, there exists a bird z that composes  *)

(*             x with y for all birds w. Prove that for all birds x, y, and  *)

(*             z, there exists a bird u such that for all w, uw = x(y(zw)). *)

(*  Refs     : [Smu85] Smullyan (1978), To Mock a Mocking Bird and Other Logi *)

(*  Source   : [ANL] *)

(*  Names    : bird5.ver1.in [ANL] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :    2 (   0 non-Horn;   2 unit;   1 RR) *)

(*             Number of atoms       :    2 (   2 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    6 (   3 constant; 0-2 arity) *)

(*             Number of variables   :    4 (   0 singleton) *)

(*             Maximal term depth    :    5 (   4 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)

(* ----For all birds x and y, there exists a bird z that composes x with  *)

(* ----y for all birds w. *)

(* ----   FAx FAy TEz FAw [response(z,w) = response(x,response(y,w))]. *)

(* ----   response(comp(x,y),w) = response(x,response(y,w)).  *)

(* ----Hypothesis: For all birds x, y, and z, there exists a bird u such  *)

(* ----that for all w, uw = x(y(zw)). *)

(* ----Finding clause (using xy to replace response(x,y)): *)

(* ----  - (FAx FAy FAz TEu FAw (uw = x(y(zw)))). *)

(* ----  TEx TEy TEz FAu TEw -(uw = x(y(zw))). *)

(* ----  Letting w = f(u), x = A, y = B, and z = C, *)

(* ----  -[(u)f(u) = A(B((C)f(u)))]. *)
ntheorem prove_bird_exists:
 (∀Univ:Type.∀U:Univ.∀W:Univ.∀X:Univ.∀Y:Univ.
∀a:Univ.
∀b:Univ.
∀c:Univ.
∀compose:∀_:Univ.∀_:Univ.Univ.
∀f:∀_:Univ.Univ.
∀response:∀_:Univ.∀_:Univ.Univ.
∀H0:∀W:Univ.∀X:Univ.∀Y:Univ.eq Univ (response (compose X Y) W) (response X (response Y W)).∃U:Univ.eq Univ (response U (f U)) (response a (response b (response c (f U)))))
.
#Univ ##.
#U ##.
#W ##.
#X ##.
#Y ##.
#a ##.
#b ##.
#c ##.
#compose ##.
#f ##.
#response ##.
#H0 ##.
napply (ex_intro ? ? ? ?) ##[
##2:
nauto by H0 ##;
##| ##skip ##]
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)
