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

set "baseuri" "cic:/matita/CoRN-Decl/model/rings/Zring".

include "CoRN.ma".

(* $Id: Zring.v,v 1.6 2004/04/08 08:20:34 lcf Exp $ *)

include "model/abgroups/Zabgroup.ma".

include "algebra/CRings.ma".

(*#* **Example of a ring: $\langle$#&lang;#[Z],[[+]],[[*]]$\rangle$#&rang;#

The multiplication and the addition are distributive.
*)

inline "cic:/CoRN/model/rings/Zring/Z_mult_plus_is_dist.con".

inline "cic:/CoRN/model/rings/Zring/Z_is_CRing.con".

inline "cic:/CoRN/model/rings/Zring/Z_as_CRing.con".

(*#* The term [Z_as_CRing] is of type [CRing]. Hence we have proven that [Z] is a constructive ring. *)

