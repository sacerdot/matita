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

set "baseuri" "cic:/matita/CoRN-Decl/model/structures/Qpossec".

include "CoRN.ma".

(* $Id: Qpossec.v,v 1.5 2004/04/06 15:46:05 lcf Exp $ *)

(*#* printing Qpos $\mathbb{Q}^{+}$ #Q<SUP>+</SUP># *)

include "model/structures/Qsec.ma".

include "algebra/CLogic.ma".

(*#* **About [Qpos]
We will prove some lemmas concerning rationals bigger than 0.

***Constants
One, two and four are all bigger than zero.
*)

inline "cic:/CoRN/model/structures/Qpossec/pos_QONE.con".

inline "cic:/CoRN/model/structures/Qpossec/pos_QTWO.con".

inline "cic:/CoRN/model/structures/Qpossec/pos_QFOUR.con".

(*#* A positive rational is not zero.
*)

inline "cic:/CoRN/model/structures/Qpossec/pos_imp_nonzero.con".

(*#* ***Multiplication
The product of two positive rationals is again positive.
*)

inline "cic:/CoRN/model/structures/Qpossec/Qmult_pres_pos0.con".

(*#* ***Inverse
The inverse of a positive rational is again positive.
*)

inline "cic:/CoRN/model/structures/Qpossec/inv_pres_pos0.con".

(*#* ***Special multiplication
Now we will investigate the function $(x,y) \mapsto xy/2$#(x,y)
&#x21A6; xy/2#. We will see that its unit is 2. Its inverse map is $x
\mapsto 4/x$ #x &#x21A6; 4/x#.
*)

inline "cic:/CoRN/model/structures/Qpossec/QTWOpos_is_rht_unit0.con".

inline "cic:/CoRN/model/structures/Qpossec/QTWOpos_is_left_unit0.con".

inline "cic:/CoRN/model/structures/Qpossec/multdiv2_is_inv.con".

