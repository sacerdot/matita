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

set "baseuri" "cic:/matita/CoRN-Decl/model/setoids/Qpossetoid".

include "CoRN.ma".

(* $Id: Qpossetoid.v,v 1.4 2004/04/06 15:46:05 lcf Exp $ *)

include "model/setoids/Qsetoid.ma".

include "algebra/CSetoidFun.ma".

include "model/structures/Qpossec.ma".

(*#* **Example of a setoid: [Qpos]
***Setoid
We will examine the subsetoid of positive rationals of the setoid of 
rational numbers.
*)

inline "cic:/CoRN/model/setoids/Qpossetoid/Qpos.con".

inline "cic:/CoRN/model/setoids/Qpossetoid/QposP.con".

(*#* One, two and four are elements of it.
*)

inline "cic:/CoRN/model/setoids/Qpossetoid/QONEpos.con".

inline "cic:/CoRN/model/setoids/Qpossetoid/QTWOpos.con".

inline "cic:/CoRN/model/setoids/Qpossetoid/QFOURpos.con".

(*#* ***Multiplication
As we have seen, multiplication preserves positivity, so we can restrict it
 to the positive rationals. We see that this restricted multiplication has some
 nice properties.
*)

inline "cic:/CoRN/model/setoids/Qpossetoid/Qmult_pres_pos1.con".

inline "cic:/CoRN/model/setoids/Qpossetoid/Qpos_mult.con".

inline "cic:/CoRN/model/setoids/Qpossetoid/associative_Qpos_mult.con".

(*#* ***Inverse
We restrict the domain of the inverse to the set of positive rationals.
*)

inline "cic:/CoRN/model/setoids/Qpossetoid/Qpos_inv.con".

(*#* The restricted inverse preserves positivity.
*)

inline "cic:/CoRN/model/setoids/Qpossetoid/inv_pres_pos1.con".

(*#* Now, we can also restrict the co-domain.
*)

inline "cic:/CoRN/model/setoids/Qpossetoid/Qpos_Qpos_inv.con".

(*#* This restricted inverse map appears a setoid function.
*)

inline "cic:/CoRN/model/setoids/Qpossetoid/Qpos_Qpos_inv_strong_ext.con".

inline "cic:/CoRN/model/setoids/Qpossetoid/Qpos_Qpos_inv_op.con".

(*#* ***Special multiplication and inverse
We define [multdiv2]: $(x,y) \mapsto xy/2$ #(x,y) &#x21A6; xy/2#.
*)

inline "cic:/CoRN/model/setoids/Qpossetoid/Qpos_div2.con".

inline "cic:/CoRN/model/setoids/Qpossetoid/multdiv2.con".

inline "cic:/CoRN/model/setoids/Qpossetoid/associative_multdiv2.con".

(*#* And its inverse [multdiv4]: $x \mapsto 4/x$ #x &#x21A6; 4/x#.
*)

inline "cic:/CoRN/model/setoids/Qpossetoid/mult4.con".

inline "cic:/CoRN/model/setoids/Qpossetoid/divmult4.con".

