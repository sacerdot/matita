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

set "baseuri" "cic:/matita/CoRN-Decl/reals/CReals".

include "CoRN.ma".

(* $Id: CReals.v,v 1.2 2004/04/05 11:35:38 lcf Exp $ *)

(*#* printing Lim %\ensuremath{\lim}% *)

include "algebra/COrdCauchy.ma".

(*#* * Definition of the notion of reals
The reals are defined as a Cauchy-closed Archimedean constructive 
ordered field in which we have a maximum function. The maximum
function is definable, using countable choice, but in a rather tricky
way. Cauchy completeness is stated by assuming a function [lim]
that returns a real number for every Cauchy sequence together with a
proof that this number is the limit.  
*)

(* Begin_SpecReals *)

inline "cic:/CoRN/reals/CReals/is_CReals.ind".

inline "cic:/CoRN/reals/CReals/CReals.ind".

coercion cic:/matita/CoRN-Decl/reals/CReals/crl_crr.con 0 (* compounds *).

(* End_SpecReals *)

inline "cic:/CoRN/reals/CReals/Lim.con".

(* UNEXPORTED
Implicit Arguments Lim [IR].
*)

