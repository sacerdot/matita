include "logic/equality.ma".

(* Inclusion of: COL052-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : COL052-1 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Combinatory Logic *)

(*  Problem  : A Question on Agreeable Birds *)

(*  Version  : Especial. *)

(*             Theorem formulation : Implicit definition of agreeable. *)

(*  English  : For all birds x and y, there exists a bird z that composes  *)

(*             x with y for all birds w. Prove that if C is agreeable then  *)

(*             A is agreeable. *)

(*  Refs     : [Smu85] Smullyan (1978), To Mock a Mocking Bird and Other Logi *)

(*  Source   : [ANL] *)

(*  Names    : bird4.ver1.in [ANL] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :    4 (   0 non-Horn;   4 unit;   2 RR) *)

(*             Number of atoms       :    4 (   4 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    7 (   4 constant; 0-2 arity) *)

(*             Number of variables   :    5 (   0 singleton) *)

(*             Maximal term depth    :    3 (   2 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)

(* ----For all birds x and y, there exists a bird z that composes x with  *)

(* ----y for all birds w. *)

(* ----   FAx FAy TEz FAw [response(z,w) = response(x,response(y,w))]. *)

(* ----   response(comp(x,y),w) = response(x,response(y,w)).  *)

(* ----Hypothesis: If C is agreeable then A is agreeable. *)

(* ----   -[ If FAx TEy (response(C,y) = response(x,y)), *)

(* ----      then FAw TEv (response(A,v) = response(w,v)) ]. *)

(* ----   -[ TEx FAy -(response(C,y) = response(x,y)) | *)

(* ----      FAw TEv (response(A,v) = response(w,v)) ]. *)

(* ----   FAx TEy (response(C,y) = response(x,y)) and *)

(* ----      TEw FAv -(response(A,v) = response(w,v). *)

(* ----   response(C,commom_bird(x)) = response(x,common_bird(x)) and *)

(* ----      -(response(A,v) = response(odd_bird,v)). *)
ntheorem prove_a_is_agreeable:
 (∀Univ:Type.∀V:Univ.∀W:Univ.∀X:Univ.∀Y:Univ.
∀a:Univ.
∀c:Univ.
∀common_bird:∀_:Univ.Univ.
∀compose:∀_:Univ.∀_:Univ.Univ.
∀odd_bird:Univ.
∀response:∀_:Univ.∀_:Univ.Univ.
∀H0:∀X:Univ.eq Univ (response c (common_bird X)) (response X (common_bird X)).
∀H1:∀W:Univ.∀X:Univ.∀Y:Univ.eq Univ (response (compose X Y) W) (response X (response Y W)).∃V:Univ.eq Univ (response a V) (response odd_bird V))
.
#Univ ##.
#V ##.
#W ##.
#X ##.
#Y ##.
#a ##.
#c ##.
#common_bird ##.
#compose ##.
#odd_bird ##.
#response ##.
#H0 ##.
#H1 ##.
napply (ex_intro ? ? ? ?) ##[
##2:
nauto by H0,H1 ##;
##| ##skip ##]
ntry (nassumption) ##;
nqed.

(* ----C composes A with B. WHY is this here?  *)

(* -------------------------------------------------------------------------- *)
