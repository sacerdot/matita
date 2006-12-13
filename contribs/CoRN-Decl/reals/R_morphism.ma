(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

(* This file was automatically generated: do not edit *********************)

set "baseuri" "cic:/matita/CoRN-Decl/reals/R_morphism".

include "CoRN.ma".

(* begin hide *)

(* In this file a notion of morphism between two arbitrary real number 
   structures, is introduced together with te proofs that this notion of 
   morphism preserves the basic algebraic structure. *)

include "reals/CReals.ma".

(* This comes from CReals1.v *)

inline "cic:/CoRN/reals/R_morphism/Cauchy_Lim_prop2.con".

(* UNEXPORTED
Section morphism
*)

alias id "R1" = "cic:/CoRN/reals/R_morphism/morphism/R1.var".

alias id "R2" = "cic:/CoRN/reals/R_morphism/morphism/R2.var".

(* UNEXPORTED
Section morphism_details
*)

alias id "phi" = "cic:/CoRN/reals/R_morphism/morphism/morphism_details/phi.var".

alias id "p1" = "cic:/CoRN/reals/R_morphism/morphism/morphism_details/p1.var".

alias id "p2" = "cic:/CoRN/reals/R_morphism/morphism/morphism_details/p2.var".

alias id "f1" = "cic:/CoRN/reals/R_morphism/morphism/morphism_details/f1.var".

alias id "f2" = "cic:/CoRN/reals/R_morphism/morphism/morphism_details/f2.var".

alias id "g1" = "cic:/CoRN/reals/R_morphism/morphism/morphism_details/g1.var".

alias id "g2" = "cic:/CoRN/reals/R_morphism/morphism/morphism_details/g2.var".

inline "cic:/CoRN/reals/R_morphism/fun_pres_relation.con".

inline "cic:/CoRN/reals/R_morphism/fun_pres_un_fun.con".

inline "cic:/CoRN/reals/R_morphism/fun_pres_bin_fun.con".

(*
Definition fun_pres_partial_fun:=(x:R1;H1:x[#]Zero;H2:(phi x)[#]Zero)
(phi (nzinj R1 (i1 (nzpro R1 x H1))))[=](nzinj R2 (i2 (nzpro R2 (phi x) H2))).
*)

inline "cic:/CoRN/reals/R_morphism/fun_pres_Lim.con".

(* UNEXPORTED
End morphism_details
*)

inline "cic:/CoRN/reals/R_morphism/Homomorphism.ind".

coercion cic:/matita/CoRN-Decl/reals/R_morphism/map.con 0 (* compounds *).

(* This might be useful later... 
Definition Homo_as_CSetoid_fun:=
    [f:Homomorphism]
         (Build_CSetoid_fun R1 R2 f 
           (fun_strext_imp_wd R1 R2 f (!map_strext f))
           (!map_strext f)
          ).
*****************)

inline "cic:/CoRN/reals/R_morphism/map_strext_unfolded.con".

inline "cic:/CoRN/reals/R_morphism/map_wd_unfolded.con".

inline "cic:/CoRN/reals/R_morphism/map_pres_less_unfolded.con".

inline "cic:/CoRN/reals/R_morphism/map_pres_plus_unfolded.con".

inline "cic:/CoRN/reals/R_morphism/map_pres_mult_unfolded.con".

(* Now we start to derive some useful properties of a Homomorphism *)

inline "cic:/CoRN/reals/R_morphism/map_pres_zero.con".

inline "cic:/CoRN/reals/R_morphism/map_pres_zero_unfolded.con".

inline "cic:/CoRN/reals/R_morphism/map_pres_minus.con".

inline "cic:/CoRN/reals/R_morphism/map_pres_minus_unfolded.con".

inline "cic:/CoRN/reals/R_morphism/map_pres_apartness.con".

(* Merely a useful special case *)

inline "cic:/CoRN/reals/R_morphism/map_pres_ap_zero.con".

inline "cic:/CoRN/reals/R_morphism/map_pres_one.con".

inline "cic:/CoRN/reals/R_morphism/map_pres_one_unfolded.con".

(* I will not use the following lemma *)

inline "cic:/CoRN/reals/R_morphism/map_pres_inv_unfolded.con".

(* UNEXPORTED
End morphism
*)

(* UNEXPORTED
Section composition
*)

alias id "R1" = "cic:/CoRN/reals/R_morphism/composition/R1.var".

alias id "R2" = "cic:/CoRN/reals/R_morphism/composition/R2.var".

alias id "R3" = "cic:/CoRN/reals/R_morphism/composition/R3.var".

alias id "f" = "cic:/CoRN/reals/R_morphism/composition/f.var".

alias id "g" = "cic:/CoRN/reals/R_morphism/composition/g.var".

inline "cic:/CoRN/reals/R_morphism/compose.con".

inline "cic:/CoRN/reals/R_morphism/compose_strext.con".

inline "cic:/CoRN/reals/R_morphism/compose_pres_less.con".

inline "cic:/CoRN/reals/R_morphism/compose_pres_plus.con".

inline "cic:/CoRN/reals/R_morphism/compose_pres_mult.con".

inline "cic:/CoRN/reals/R_morphism/compose_pres_Lim.con".

inline "cic:/CoRN/reals/R_morphism/Compose.con".

(* UNEXPORTED
End composition
*)

(* UNEXPORTED
Section isomorphism
*)

alias id "R1" = "cic:/CoRN/reals/R_morphism/isomorphism/R1.var".

alias id "R2" = "cic:/CoRN/reals/R_morphism/isomorphism/R2.var".

(* UNEXPORTED
Section identity_map
*)

alias id "R3" = "cic:/CoRN/reals/R_morphism/isomorphism/identity_map/R3.var".

alias id "f" = "cic:/CoRN/reals/R_morphism/isomorphism/identity_map/f.var".

inline "cic:/CoRN/reals/R_morphism/map_is_id.con".

(* UNEXPORTED
End identity_map
*)

inline "cic:/CoRN/reals/R_morphism/Isomorphism.ind".

(* UNEXPORTED
End isomorphism
*)

(* UNEXPORTED
Section surjective_map
*)

alias id "R1" = "cic:/CoRN/reals/R_morphism/surjective_map/R1.var".

alias id "R2" = "cic:/CoRN/reals/R_morphism/surjective_map/R2.var".

alias id "f" = "cic:/CoRN/reals/R_morphism/surjective_map/f.var".

inline "cic:/CoRN/reals/R_morphism/map_is_surjective.con".

(* UNEXPORTED
End surjective_map
*)

(* UNEXPORTED
Section simplification
*)

alias id "R1" = "cic:/CoRN/reals/R_morphism/simplification/R1.var".

alias id "R2" = "cic:/CoRN/reals/R_morphism/simplification/R2.var".

alias id "f" = "cic:/CoRN/reals/R_morphism/simplification/f.var".

alias id "H1" = "cic:/CoRN/reals/R_morphism/simplification/H1.var".

inline "cic:/CoRN/reals/R_morphism/f_well_def.con".

(* UNEXPORTED
Section with_less
*)

alias id "H2" = "cic:/CoRN/reals/R_morphism/simplification/with_less/H2.var".

inline "cic:/CoRN/reals/R_morphism/less_pres_f.con".

inline "cic:/CoRN/reals/R_morphism/leEq_pres_f.con".

inline "cic:/CoRN/reals/R_morphism/f_pres_leEq.con".

inline "cic:/CoRN/reals/R_morphism/f_pres_apartness.con".

(* UNEXPORTED
End with_less
*)

(* UNEXPORTED
Section with_plus
*)

alias id "H3" = "cic:/CoRN/reals/R_morphism/simplification/with_plus/H3.var".

inline "cic:/CoRN/reals/R_morphism/f_pres_Zero.con".

inline "cic:/CoRN/reals/R_morphism/f_pres_minus.con".

inline "cic:/CoRN/reals/R_morphism/f_pres_min.con".

(* UNEXPORTED
End with_plus
*)

(* UNEXPORTED
Section with_plus_less
*)

alias id "H2" = "cic:/CoRN/reals/R_morphism/simplification/with_plus_less/H2.var".

alias id "H3" = "cic:/CoRN/reals/R_morphism/simplification/with_plus_less/H3.var".

inline "cic:/CoRN/reals/R_morphism/f_pres_ap_zero.con".

(* UNEXPORTED
Section surjectivity_helps
*)

alias id "f_surj" = "cic:/CoRN/reals/R_morphism/simplification/with_plus_less/surjectivity_helps/f_surj.var".

inline "cic:/CoRN/reals/R_morphism/f_pres_Lim.con".

(* UNEXPORTED
End surjectivity_helps
*)

(* UNEXPORTED
Section with_mult_plus_less
*)

alias id "H4" = "cic:/CoRN/reals/R_morphism/simplification/with_plus_less/with_mult_plus_less/H4.var".

inline "cic:/CoRN/reals/R_morphism/f_pres_one.con".

inline "cic:/CoRN/reals/R_morphism/f_pres_inv.con".

inline "cic:/CoRN/reals/R_morphism/simplified_Homomorphism.con".

(* UNEXPORTED
End with_mult_plus_less
*)

(* UNEXPORTED
End with_plus_less
*)

(* UNEXPORTED
End simplification
*)

(* end hide *)

