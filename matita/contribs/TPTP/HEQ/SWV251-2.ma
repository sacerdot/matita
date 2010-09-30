set "baseuri" "cic:/matita/TPTP/SWV251-2".
include "logic/equality.ma".

(* Inclusion of: SWV251-2.p *)

(* ------------------------------------------------------------------------------ *)

(*  File     : SWV251-2 : TPTP v3.2.0. Released v3.2.0. *)

(*  Domain   : Software Verification *)

(*  Problem  : Cryptographic protocol problem for messages *)

(*  Version  : [Pau06] axioms : Reduced > Especial. *)

(*  English  : *)

(*  Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe *)

(*  Source   : [Pau06] *)

(*  Names    :  *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.43 v3.2.0 *)

(*  Syntax   : Number of clauses     :   13 (   0 non-Horn;   6 unit;   9 RR) *)

(*             Number of atoms       :   23 (   4 equality) *)

(*             Maximal clause size   :    3 (   2 average) *)

(*             Number of predicates  :    3 (   0 propositional; 2-3 arity) *)

(*             Number of functors    :   11 (   5 constant; 0-3 arity) *)

(*             Number of variables   :   60 (  47 singleton) *)

(*             Maximal term depth    :    5 (   2 average) *)

(*  Comments : The problems in the [Pau06] collection each have very many axioms, *)

(*             of which only a small selection are required for the refutation. *)

(*             The mission is to find those few axioms, after which a refutation *)

(*             can be quite easily found. This version has only the necessary *)

(*             axioms. *)

(* ------------------------------------------------------------------------------ *)
theorem cls_conjecture_2:
 ∀Univ:Set.∀T_a:Univ.∀V_A:Univ.∀V_B:Univ.∀V_C:Univ.∀V_G:Univ.∀V_H:Univ.∀V_c:Univ.∀V_x:Univ.∀c_Message_Oanalz:∀_:Univ.Univ.∀c_Message_Osynth:∀_:Univ.Univ.∀c_in:∀_:Univ.∀_:Univ.∀_:Univ.Prop.∀c_insert:∀_:Univ.∀_:Univ.∀_:Univ.Univ.∀c_lessequals:∀_:Univ.∀_:Univ.∀_:Univ.Prop.∀c_minus:∀_:Univ.∀_:Univ.∀_:Univ.Univ.∀c_union:∀_:Univ.∀_:Univ.∀_:Univ.Univ.∀tc_Message_Omsg:Univ.∀tc_set:∀_:Univ.Univ.∀v_G:Univ.∀v_H:Univ.∀v_X:Univ.∀v_x:Univ.∀H0:c_in v_x (c_Message_Oanalz (c_insert v_X v_H tc_Message_Omsg)) tc_Message_Omsg.∀H1:c_in v_X (c_Message_Osynth (c_Message_Oanalz v_G)) tc_Message_Omsg.∀H2:∀T_a:Univ.∀V_A:Univ.c_lessequals V_A V_A (tc_set T_a).∀H3:∀T_a:Univ.∀V_A:Univ.∀V_B:Univ.∀_:c_lessequals V_A V_B (tc_set T_a).∀_:c_lessequals V_B V_A (tc_set T_a).eq Univ V_A V_B.∀H4:∀T_a:Univ.∀V_A:Univ.∀V_B:Univ.∀V_c:Univ.∀_:c_lessequals V_A V_B (tc_set T_a).∀_:c_in V_c V_A T_a.c_in V_c V_B T_a.∀H5:∀T_a:Univ.∀V_A:Univ.∀V_B:Univ.∀V_x:Univ.∀_:c_in V_x V_B T_a.eq Univ (c_minus (c_insert V_x V_A T_a) V_B (tc_set T_a)) (c_minus V_A V_B (tc_set T_a)).∀H6:∀T_a:Univ.∀V_A:Univ.∀V_B:Univ.∀V_C:Univ.∀_:c_lessequals V_A V_C (tc_set T_a).∀_:c_lessequals V_B V_C (tc_set T_a).c_lessequals (c_union V_A V_B T_a) V_C (tc_set T_a).∀H7:∀T_a:Univ.∀V_A:Univ.∀V_B:Univ.∀V_C:Univ.∀_:c_lessequals (c_union V_A V_B T_a) V_C (tc_set T_a).c_lessequals V_B V_C (tc_set T_a).∀H8:∀T_a:Univ.∀V_A:Univ.∀V_B:Univ.∀V_C:Univ.∀_:c_lessequals (c_union V_A V_B T_a) V_C (tc_set T_a).c_lessequals V_A V_C (tc_set T_a).∀H9:∀T_a:Univ.∀V_A:Univ.∀V_B:Univ.eq Univ (c_union V_A (c_minus V_B V_A (tc_set T_a)) T_a) (c_union V_A V_B T_a).∀H10:∀T_a:Univ.∀V_A:Univ.∀V_B:Univ.eq Univ (c_union (c_minus V_B V_A (tc_set T_a)) V_A T_a) (c_union V_B V_A T_a).∀H11:∀V_G:Univ.∀V_H:Univ.∀_:c_lessequals V_G V_H (tc_set tc_Message_Omsg).c_lessequals (c_Message_Oanalz V_G) (c_Message_Oanalz V_H) (tc_set tc_Message_Omsg).c_in v_x (c_Message_Oanalz (c_union (c_Message_Osynth (c_Message_Oanalz v_G)) v_H tc_Message_Omsg)) tc_Message_Omsg
.
intros.
autobatch depth=5 width=5 size=20 timeout=10;
try assumption.
print proofterm.
qed.

(* ------------------------------------------------------------------------------ *)
