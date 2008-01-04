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

set "baseuri" "cic:/matita/CoRN-Decl/model/structures/Nsec".

include "CoRN.ma".

(* $Id: Nsec.v,v 1.6 2004/04/06 15:46:05 lcf Exp $ *)

(*#* printing {#N} $\ensuremath{\mathrel\#_{\mathbb N}}$ *)

include "algebra/CLogic.ma".

(*#* *[nat]
**About [nat]

We prove some basic lemmas of the natural numbers.

A variant of [0_S] from the standard library
*)

inline "cic:/CoRN/model/structures/Nsec/S_O.con".

(*#* ***Apartness
*)

inline "cic:/CoRN/model/structures/Nsec/ap_nat.con".

(* NOTATION
Infix "{#N}" := ap_nat (no associativity, at level 90).
*)

inline "cic:/CoRN/model/structures/Nsec/ap_nat_irreflexive0.con".

inline "cic:/CoRN/model/structures/Nsec/ap_nat_symmetric0.con".

inline "cic:/CoRN/model/structures/Nsec/ap_nat_cotransitive0.con".

inline "cic:/CoRN/model/structures/Nsec/ap_nat_tight0.con".

(*#* ***Addition
*)

inline "cic:/CoRN/model/structures/Nsec/plus_strext0.con".

(*#* There is no inverse for addition, because every candidate will fail for 2
*)

inline "cic:/CoRN/model/structures/Nsec/no_inverse0.con".

(*#* ***Multiplication
*)

inline "cic:/CoRN/model/structures/Nsec/mult_strext0.con".

