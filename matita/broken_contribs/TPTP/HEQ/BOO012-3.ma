set "baseuri" "cic:/matita/TPTP/BOO012-3".
include "logic/equality.ma".

(* Inclusion of: BOO012-3.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : BOO012-3 : TPTP v3.2.0. Bugfixed v1.2.1. *)

(*  Domain   : Boolean Algebra *)

(*  Problem  : Inverse is an involution *)

(*  Version  : [MOW76] axioms : Augmented. *)

(*  English  :  *)

(*  Refs     : [Whi61] Whitesitt (1961), Boolean Algebra and Its Applications *)

(*           : [MOW76] McCharen et al. (1976), Problems and Experiments for a *)

(*  Source   : [MOW76] *)

(*  Names    : B8 [MOW76] *)

(*           : prob8.ver1 [ANL] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v3.1.0, 0.22 v2.7.0, 0.00 v2.4.0, 0.17 v2.3.0, 0.33 v2.2.1, 0.62 v2.2.0, 0.50 v2.1.0, 0.33 v2.0.0 *)

(*  Syntax   : Number of clauses     :   35 (   0 non-Horn;  17 unit;  19 RR) *)

(*             Number of atoms       :   87 (   3 equality) *)

(*             Maximal clause size   :    5 (   2 average) *)

(*             Number of predicates  :    3 (   0 propositional; 2-3 arity) *)

(*             Number of functors    :    6 (   3 constant; 0-2 arity) *)

(*             Number of variables   :  120 (   6 singleton) *)

(*             Maximal term depth    :    3 (   1 average) *)

(*  Comments :  *)

(*  Bugfixes : v1.2.1 - Clause x_plus_multiplicative_identity fixed. *)

(* -------------------------------------------------------------------------- *)

(* ----Include boolean algebra axioms  *)

(* Inclusion of: Axioms/BOO002-0.ax *)

(* -------------------------------------------------------------------------- *)

(*  File     : BOO002-0 : TPTP v3.2.0. Released v1.0.0. *)

(*  Domain   : Boolean Algebra *)

(*  Axioms   : Boolean algebra axioms *)

(*  Version  : [MOW76] axioms. *)

(*  English  :  *)

(*  Refs     : [Whi61] Whitesitt (1961), Boolean Algebra and Its Applications *)

(*           : [MOW76] McCharen et al. (1976), Problems and Experiments for a *)

(*  Source   : [MOW76] *)

(*  Names    :  *)

(*  Status   :  *)

(*  Syntax   : Number of clauses    :   22 (   0 non-Horn;  10 unit;  12 RR) *)

(*             Number of literals   :   60 (   2 equality) *)

(*             Maximal clause size  :    5 (   3 average) *)

(*             Number of predicates :    3 (   0 propositional; 2-3 arity) *)

(*             Number of functors   :    5 (   2 constant; 0-2 arity) *)

(*             Number of variables  :   82 (   0 singleton) *)

(*             Maximal term depth   :    2 (   1 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)

(* -----Well definedness of the operations  *)

(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
theorem prove_inverse_is_an_involution:
 ∀Univ:Set.∀U:Univ.∀V:Univ.∀V1:Univ.∀V2:Univ.∀V3:Univ.∀V4:Univ.∀X:Univ.∀X_plus_Y:Univ.∀X_plus_Y_plus_Z:Univ.∀X_times_Y:Univ.∀X_times_Y_times_Z:Univ.∀Y:Univ.∀Y_plus_Z:Univ.∀Y_times_Z:Univ.∀Z:Univ.∀add:∀_:Univ.∀_:Univ.Univ.∀additive_identity:Univ.∀inverse:∀_:Univ.Univ.∀multiplicative_identity:Univ.∀multiply:∀_:Univ.∀_:Univ.Univ.∀product:∀_:Univ.∀_:Univ.∀_:Univ.Prop.∀sum:∀_:Univ.∀_:Univ.∀_:Univ.Prop.∀x:Univ.∀H0:∀X:Univ.∀X_times_Y:Univ.∀X_times_Y_times_Z:Univ.∀Y:Univ.∀Y_times_Z:Univ.∀Z:Univ.∀_:product X Y_times_Z X_times_Y_times_Z.∀_:product Y Z Y_times_Z.∀_:product X Y X_times_Y.product X_times_Y Z X_times_Y_times_Z.∀H1:∀X:Univ.∀X_times_Y:Univ.∀X_times_Y_times_Z:Univ.∀Y:Univ.∀Y_times_Z:Univ.∀Z:Univ.∀_:product X Y_times_Z X_times_Y_times_Z.∀_:product Y Z Y_times_Z.∀_:product X Y X_times_Y.product X_times_Y Z X_times_Y_times_Z.∀H2:∀X:Univ.∀X_plus_Y:Univ.∀X_plus_Y_plus_Z:Univ.∀Y:Univ.∀Y_plus_Z:Univ.∀Z:Univ.∀_:sum X Y_plus_Z X_plus_Y_plus_Z.∀_:sum Y Z Y_plus_Z.∀_:sum X Y X_plus_Y.sum X_plus_Y Z X_plus_Y_plus_Z.∀H3:∀X:Univ.∀X_plus_Y:Univ.∀X_plus_Y_plus_Z:Univ.∀Y:Univ.∀Y_plus_Z:Univ.∀Z:Univ.∀_:sum X Y_plus_Z X_plus_Y_plus_Z.∀_:sum Y Z Y_plus_Z.∀_:sum X Y X_plus_Y.sum X_plus_Y Z X_plus_Y_plus_Z.∀H4:∀X:Univ.∀Y:Univ.product X (add X Y) X.∀H5:∀X:Univ.∀Y:Univ.sum X (multiply X Y) X.∀H6:∀X:Univ.∀Y:Univ.∀Z:Univ.∀_:sum X Y Z.product X Z X.∀H7:∀X:Univ.∀Y:Univ.∀Z:Univ.∀_:product X Y Z.sum X Z X.∀H8:∀X:Univ.product X additive_identity additive_identity.∀H9:∀X:Univ.sum X multiplicative_identity multiplicative_identity.∀H10:∀X:Univ.product X X X.∀H11:∀X:Univ.sum X X X.∀H12:∀U:Univ.∀V:Univ.∀X:Univ.∀Y:Univ.∀_:product X Y V.∀_:product X Y U.eq Univ U V.∀H13:∀U:Univ.∀V:Univ.∀X:Univ.∀Y:Univ.∀_:sum X Y V.∀_:sum X Y U.eq Univ U V.∀H14:∀X:Univ.product X (inverse X) additive_identity.∀H15:∀X:Univ.product (inverse X) X additive_identity.∀H16:∀X:Univ.sum X (inverse X) multiplicative_identity.∀H17:∀X:Univ.sum (inverse X) X multiplicative_identity.∀H18:∀V1:Univ.∀V2:Univ.∀V3:Univ.∀V4:Univ.∀X:Univ.∀Y:Univ.∀Z:Univ.∀_:product V1 V2 V4.∀_:product Y Z V3.∀_:sum Z X V2.∀_:sum Y X V1.sum V3 X V4.∀H19:∀V1:Univ.∀V2:Univ.∀V3:Univ.∀V4:Univ.∀X:Univ.∀Y:Univ.∀Z:Univ.∀_:sum V3 X V4.∀_:product Y Z V3.∀_:sum Z X V2.∀_:sum Y X V1.product V1 V2 V4.∀H20:∀V1:Univ.∀V2:Univ.∀V3:Univ.∀V4:Univ.∀X:Univ.∀Y:Univ.∀Z:Univ.∀_:product V1 V2 V4.∀_:product Y Z V3.∀_:sum X Z V2.∀_:sum X Y V1.sum X V3 V4.∀H21:∀V1:Univ.∀V2:Univ.∀V3:Univ.∀V4:Univ.∀X:Univ.∀Y:Univ.∀Z:Univ.∀_:sum X V3 V4.∀_:product Y Z V3.∀_:sum X Z V2.∀_:sum X Y V1.product V1 V2 V4.∀H22:∀V1:Univ.∀V2:Univ.∀V3:Univ.∀V4:Univ.∀X:Univ.∀Y:Univ.∀Z:Univ.∀_:sum V1 V2 V4.∀_:sum Y Z V3.∀_:product Z X V2.∀_:product Y X V1.product V3 X V4.∀H23:∀V1:Univ.∀V2:Univ.∀V3:Univ.∀V4:Univ.∀X:Univ.∀Y:Univ.∀Z:Univ.∀_:product V3 X V4.∀_:sum Y Z V3.∀_:product Z X V2.∀_:product Y X V1.sum V1 V2 V4.∀H24:∀V1:Univ.∀V2:Univ.∀V3:Univ.∀V4:Univ.∀X:Univ.∀Y:Univ.∀Z:Univ.∀_:sum V1 V2 V4.∀_:sum Y Z V3.∀_:product X Z V2.∀_:product X Y V1.product X V3 V4.∀H25:∀V1:Univ.∀V2:Univ.∀V3:Univ.∀V4:Univ.∀X:Univ.∀Y:Univ.∀Z:Univ.∀_:product X V3 V4.∀_:sum Y Z V3.∀_:product X Z V2.∀_:product X Y V1.sum V1 V2 V4.∀H26:∀X:Univ.product X multiplicative_identity X.∀H27:∀X:Univ.product multiplicative_identity X X.∀H28:∀X:Univ.sum X additive_identity X.∀H29:∀X:Univ.sum additive_identity X X.∀H30:∀X:Univ.∀Y:Univ.∀Z:Univ.∀_:product X Y Z.product Y X Z.∀H31:∀X:Univ.∀Y:Univ.∀Z:Univ.∀_:sum X Y Z.sum Y X Z.∀H32:∀X:Univ.∀Y:Univ.product X Y (multiply X Y).∀H33:∀X:Univ.∀Y:Univ.sum X Y (add X Y).eq Univ (inverse (inverse x)) x
.
intros.
autobatch depth=5 width=5 size=20 timeout=10;
try assumption.
print proofterm.
qed.

(* -------------------------------------------------------------------------- *)
