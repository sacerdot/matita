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

set "baseuri" "cic:/matita/CoRN-Decl/model/reals/Cauchy_IR".

include "CoRN.ma".

(* $Id: Cauchy_IR.v,v 1.2 2004/04/06 15:46:03 lcf Exp $ *)

include "model/ordfields/Qordfield.ma".

include "reals/Cauchy_CReals.ma".

(*#* * Cauchy Real Numbers
Earlier we defined a construction of a real number structure from an
arbitrary archimedian ordered field.  Plugging in [Q] we get the model
of the real numbers as Cauchy sequences of rationals.
*)

inline "cic:/CoRN/model/reals/Cauchy_IR/Cauchy_IR.con".

(*#* The term [Cauchy_IR] is of type [CReals]. *)

