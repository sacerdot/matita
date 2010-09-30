set "baseuri" "cic:/matita/TPTP/HWV002-1".
include "logic/equality.ma".

(* Inclusion of: HWV002-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : HWV002-1 : TPTP v3.2.0. Released v1.1.0. *)

(*  Domain   : Hardware Verification *)

(*  Problem  : Invert 3 inputs with 2 not gates *)

(*  Version  : [ANL] axioms : Reduced > Complete. *)

(*  English  : This is made to validate the circuit that inverts 3 inputs  *)

(*             using as many AND and OR gates as you like, but using only  *)

(*             two NOT gates. *)

(*  Refs     : [WO+92] Wos et al. (1992), Automated Reasoning: Introduction a *)

(*  Source   : [ANL] *)

(*  Names    : two.inverter.val.ver1.in [ANL] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.43 v3.1.0, 0.56 v2.7.0, 0.67 v2.6.0, 0.57 v2.5.0, 0.40 v2.4.0, 0.67 v2.2.1, 1.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :   51 (   0 non-Horn;  50 unit;  34 RR) *)

(*             Number of atoms       :   53 (  47 equality) *)

(*             Maximal clause size   :    3 (   1 average) *)

(*             Number of predicates  :    2 (   0 propositional; 1-2 arity) *)

(*             Number of functors    :   39 (  35 constant; 0-2 arity) *)

(*             Number of variables   :   28 (   2 singleton) *)

(*             Maximal term depth    :    3 (   2 average) *)

(*  Comments : Some duplicate clauses have been removed from the [ANL] version. *)

(* -------------------------------------------------------------------------- *)

(* ----Canonicalizing an exclusive-or/and expression  *)

(* ----Associativity and symmetry  *)

(* ----Problem clauses  *)
theorem prove_inversion:
 ∀Univ:Set.∀X:Univ.∀Y:Univ.∀Z:Univ.∀a1:Univ.∀myand:∀_:Univ.∀_:Univ.Univ.∀circuit:∀_:Univ.Prop.∀i1:Univ.∀i2:Univ.∀i3:Univ.∀inv1:Univ.∀inv2:Univ.∀n0:Univ.∀n1:Univ.∀n10:Univ.∀n11:Univ.∀n12:Univ.∀n13:Univ.∀n14:Univ.∀n15:Univ.∀n16:Univ.∀n17:Univ.∀n18:Univ.∀n19:Univ.∀n2:Univ.∀n20:Univ.∀n21:Univ.∀n22:Univ.∀n23:Univ.∀n24:Univ.∀n25:Univ.∀n3:Univ.∀n4:Univ.∀n5:Univ.∀n6:Univ.∀n7:Univ.∀n8:Univ.∀n9:Univ.∀not:∀_:Univ.Univ.∀o1:Univ.∀o2:Univ.∀o3:Univ.∀or:∀_:Univ.∀_:Univ.Univ.∀xor:∀_:Univ.∀_:Univ.Univ.∀H0:circuit o3.∀H1:circuit o2.∀H2:circuit o1.∀H3:eq Univ inv2 (not n9).∀H4:eq Univ inv1 (not n20).∀H5:eq Univ n25 (or n2 n24).∀H6:eq Univ n24 (myand i1 inv1).∀H7:eq Univ n23 (myand i1 i3).∀H8:eq Univ n22 (or n23 n6).∀H9:eq Univ n21 (myand inv1 inv2).∀H10:eq Univ n20 (or n22 n14).∀H11:eq Univ n19 (myand n23 inv2).∀H12:eq Univ n18 (or n19 n25).∀H13:eq Univ n17 (or n18 n21).∀H14:eq Univ n16 (myand n14 inv2).∀H15:eq Univ n15 (myand inv2 n6).∀H16:eq Univ n14 (myand i2 i3).∀H17:eq Univ n13 (or n12 n21).∀H18:eq Univ n12 (or n11 n16).∀H19:eq Univ n11 (or a1 n2).∀H20:eq Univ n10 (or n24 n7).∀H21:eq Univ n9 (or n8 n2).∀H22:eq Univ n8 (or a1 n10).∀H23:eq Univ n7 (myand n6 i3).∀H24:eq Univ n6 (myand i1 i2).∀H25:eq Univ n5 (or n4 n21).∀H26:eq Univ n4 (or n15 n3).∀H27:eq Univ n3 (or a1 n24).∀H28:eq Univ n2 (myand inv1 i3).∀H29:eq Univ a1 (myand inv1 i2).∀H30:eq Univ o3 n5.∀H31:eq Univ o2 n17.∀H32:eq Univ o1 n13.∀H33:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (myand Y (myand X Z)) (myand X (myand Y Z)).∀H34:∀X:Univ.∀Y:Univ.eq Univ (myand X Y) (myand Y X).∀H35:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (xor Y (xor X Z)) (xor X (xor Y Z)).∀H36:∀X:Univ.∀Y:Univ.eq Univ (xor X Y) (xor Y X).∀H37:∀X:Univ.∀Y:Univ.eq Univ (or X Y) (xor (myand X Y) (xor X Y)).∀H38:∀X:Univ.eq Univ (not X) (xor n1 X).∀H39:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (myand X (xor Y Z)) (xor (myand X Y) (myand X Z)).∀H40:∀X:Univ.∀Y:Univ.eq Univ (myand X (myand X Y)) (myand X Y).∀H41:∀X:Univ.eq Univ (myand X X) X.∀H42:∀X:Univ.eq Univ (myand X n1) X.∀H43:∀X:Univ.eq Univ (myand n1 X) X.∀H44:∀X:Univ.eq Univ (myand X n0) n0.∀H45:∀X:Univ.eq Univ (myand n0 X) n0.∀H46:∀X:Univ.∀Y:Univ.eq Univ (xor X (xor X Y)) Y.∀H47:∀X:Univ.eq Univ (xor X X) n0.∀H48:∀X:Univ.eq Univ (xor X n0) X.∀H49:∀X:Univ.eq Univ (xor n0 X) X.∀_:circuit (not i3).∀_:circuit (not i2).circuit (not i1)
.
intros.
autobatch depth=5 width=5 size=20 timeout=10;
try assumption.
print proofterm.
qed.

(* -------------------------------------------------------------------------- *)
