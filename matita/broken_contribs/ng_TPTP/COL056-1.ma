include "logic/equality.ma".

(* Inclusion of: COL056-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : COL056-1 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Combinatory Logic *)

(*  Problem  : Normal Birds *)

(*  Version  : Especial. *)

(*  English  : For all birds x and y, there exists a bird z that composes  *)

(*             x with y for all birds w. Prove that if there exists a happy  *)

(*             bird then there exists a normal bird. *)

(*  Refs     : [Smu85] Smullyan (1978), To Mock a Mocking Bird and Other Logi *)

(*  Source   : [ANL] *)

(*  Names    : bird8.ver1.in [ANL] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.11 v3.4.0, 0.12 v3.3.0, 0.07 v3.1.0, 0.00 v2.7.0, 0.09 v2.6.0, 0.17 v2.5.0, 0.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :    4 (   0 non-Horn;   4 unit;   3 RR) *)

(*             Number of atoms       :    4 (   4 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    5 (   3 constant; 0-2 arity) *)

(*             Number of variables   :    5 (   1 singleton) *)

(*             Maximal term depth    :    3 (   2 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)

(* ----For all birds x and y, there exists a bird z that composes x with  *)

(* ----y for all birds w. *)

(* ----   FAx FAy TEz FAw [response(z,w) = response(x,response(y,w))]. *)

(* ----   response(comp(x,y),w) = response(x,response(y,w)).  *)

(* ----Hypothesis: If there exists a happy bird then there exists a normal  *)

(* ----bird. *)

(* ----Finding clause (using xy to replace response(x,y)): *)

(* ----   -[ If TEx TEy TEz (xy = z) and (xz = y) *)

(* ----      then TEw TEv (wv = v) ]. *)

(* ----   -[ FAx FAy FAz -((xy = z) and (xz = y)) | TEw TEv (wv = v) ] *)

(* ----   TEx TEy TEz [(xy = z) and (xz = y)] and FAw FAv -(wv = v). *)

(* ----   (AB = C) and (AC = B) and -(wv = v). *)
ntheorem prove_there_exists_a_happy_bird:
 (∀Univ:Type.∀V:Univ.∀W:Univ.∀X:Univ.∀Y:Univ.
∀a:Univ.
∀b:Univ.
∀c:Univ.
∀compose:∀_:Univ.∀_:Univ.Univ.
∀response:∀_:Univ.∀_:Univ.Univ.
∀H0:eq Univ (response a c) b.
∀H1:eq Univ (response a b) c.
∀H2:∀W:Univ.∀X:Univ.∀Y:Univ.eq Univ (response (compose X Y) W) (response X (response Y W)).∃V:Univ.∃W:Univ.eq Univ (response W V) V)
.
#Univ ##.
#V ##.
#W ##.
#X ##.
#Y ##.
#a ##.
#b ##.
#c ##.
#compose ##.
#response ##.
#H0 ##.
#H1 ##.
#H2 ##.
napply (ex_intro ? ? ? ?) ##[
##2:
napply (ex_intro ? ? ? ?) ##[
##2:
nauto by H0,H1,H2 ##;
##| ##skip ##]
##| ##skip ##]
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)
