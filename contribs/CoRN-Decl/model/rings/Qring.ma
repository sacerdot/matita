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

set "baseuri" "cic:/matita/CoRN-Decl/model/rings/Qring".

include "CoRN.ma".

(* $Id: Qring.v,v 1.8 2004/04/23 10:01:03 lcf Exp $ *)

include "model/abgroups/Qabgroup.ma".

include "algebra/CRings.ma".

include "model/rings/Zring.ma".

(*#* **Example of a ring: $\langle$#&lang;#[Q],[[+]],[[*]]$\rangle$#&rang;#
Because [Q] forms an abelian group with addition, a monoid with 
multiplication and it satisfies the distributive law, it is a ring.
*)

inline "cic:/CoRN/model/rings/Qring/Q_mult_plus_is_dist.con".

inline "cic:/CoRN/model/rings/Qring/Q_is_CRing.con".

inline "cic:/CoRN/model/rings/Qring/Q_as_CRing.con".

(*#* The following lemmas are used in the proof that [Q] is Archimeadian.
*)

inline "cic:/CoRN/model/rings/Qring/injz_Nring.con".

inline "cic:/CoRN/model/rings/Qring/injZ_eq.con".

inline "cic:/CoRN/model/rings/Qring/nring_Q.con".

