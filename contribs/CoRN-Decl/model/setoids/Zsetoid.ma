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

set "baseuri" "cic:/matita/CoRN-Decl/model/setoids/Zsetoid".

include "CoRN.ma".

(* $Id: Zsetoid.v,v 1.5 2004/04/07 15:08:08 lcf Exp $ *)

include "model/structures/Zsec.ma".

include "algebra/CSetoidFun.ma".

(*#* **Example of a setoid: [Z]
*** [Z]
*)

inline "cic:/CoRN/model/setoids/Zsetoid/ap_Z_irreflexive.con".

inline "cic:/CoRN/model/setoids/Zsetoid/ap_Z_symmetric.con".

inline "cic:/CoRN/model/setoids/Zsetoid/ap_Z_cotransitive.con".

inline "cic:/CoRN/model/setoids/Zsetoid/ap_Z_tight.con".

inline "cic:/CoRN/model/setoids/Zsetoid/ap_Z_is_apartness.con".

inline "cic:/CoRN/model/setoids/Zsetoid/Z_as_CSetoid.con".

(*#* The term [Z_as_CSetoid] is of type [CSetoid]. Hence we have proven that [Z] is a constructive setoid.
***Addition
We will prove now that the addition on the integers is a setoid function.
*)

inline "cic:/CoRN/model/setoids/Zsetoid/Zplus_wd.con".

inline "cic:/CoRN/model/setoids/Zsetoid/Zplus_strext.con".

inline "cic:/CoRN/model/setoids/Zsetoid/Zplus_is_bin_fun.con".

(*#* What's more: the addition is also associative and commutative.
*)

inline "cic:/CoRN/model/setoids/Zsetoid/Zplus_is_assoc.con".

inline "cic:/CoRN/model/setoids/Zsetoid/Zplus_is_commut.con".

(*#* ***Opposite
Taking the opposite of an integer is a setoid function.
*)

inline "cic:/CoRN/model/setoids/Zsetoid/Zopp_wd.con".

inline "cic:/CoRN/model/setoids/Zsetoid/Zopp_strext.con".

inline "cic:/CoRN/model/setoids/Zsetoid/Zopp_is_fun.con".

(*#* ***Multiplication
Finally the multiplication is a setoid function and is associative and commutative.
*)

inline "cic:/CoRN/model/setoids/Zsetoid/Zmult_wd.con".

inline "cic:/CoRN/model/setoids/Zsetoid/Zmult_strext.con".

inline "cic:/CoRN/model/setoids/Zsetoid/Zmult_is_bin_fun.con".

inline "cic:/CoRN/model/setoids/Zsetoid/Zmult_is_assoc.con".

inline "cic:/CoRN/model/setoids/Zsetoid/Zmult_is_commut.con".

