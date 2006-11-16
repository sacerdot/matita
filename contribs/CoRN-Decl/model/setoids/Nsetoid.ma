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

set "baseuri" "cic:/matita/CoRN-Decl/model/setoids/Nsetoid".

include "CoRN.ma".

(* $Id: Nsetoid.v,v 1.4 2004/04/06 15:46:04 lcf Exp $ *)

include "model/structures/Nsec.ma".

include "algebra/CSetoidFun.ma".

(*#* **Example of a setoid: [nat]

We will show that the natural numbers form a CSetoid. 
*)

inline "cic:/CoRN/model/setoids/Nsetoid/ap_nat_irreflexive.con".

inline "cic:/CoRN/model/setoids/Nsetoid/ap_nat_symmetric.con".

inline "cic:/CoRN/model/setoids/Nsetoid/ap_nat_cotransitive.con".

inline "cic:/CoRN/model/setoids/Nsetoid/ap_nat_tight.con".

inline "cic:/CoRN/model/setoids/Nsetoid/ap_nat_is_apartness.con".

inline "cic:/CoRN/model/setoids/Nsetoid/nat_as_CSetoid.con".

(*#* ***Addition
*)

inline "cic:/CoRN/model/setoids/Nsetoid/plus_wd.con".

inline "cic:/CoRN/model/setoids/Nsetoid/plus_strext.con".

inline "cic:/CoRN/model/setoids/Nsetoid/plus_is_bin_fun.con".

(*#* It is associative and commutative.
*)

inline "cic:/CoRN/model/setoids/Nsetoid/plus_is_assoc.con".

inline "cic:/CoRN/model/setoids/Nsetoid/plus_is_commut.con".

(*#* ***Multiplication
*)

inline "cic:/CoRN/model/setoids/Nsetoid/mult_strext.con".

inline "cic:/CoRN/model/setoids/Nsetoid/mult_as_bin_fun.con".

