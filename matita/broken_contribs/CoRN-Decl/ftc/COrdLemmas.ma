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

set "baseuri" "cic:/matita/CoRN-Decl/ftc/COrdLemmas".

include "CoRN.ma".

(* $Id: COrdLemmas.v,v 1.2 2004/04/23 10:00:57 lcf Exp $ *)

include "algebra/COrdCauchy.ma".

(* UNEXPORTED
Section Lemmas
*)

(*#* *Lemmas for Integration

Here we include several lemmas valid in any ordered field [F] which 
are useful for integration.

** Merging orders

We first prove that any two strictly ordered sets of points which have
an empty intersection can be ordered as one (this will be the core of
the proof that any two partitions with no common point have a common
refinement).
*)

alias id "F" = "cic:/CoRN/ftc/COrdLemmas/Lemmas/F.var".

inline "cic:/CoRN/ftc/COrdLemmas/om_fun_lt.con".

inline "cic:/CoRN/ftc/COrdLemmas/om_fun.con".

inline "cic:/CoRN/ftc/COrdLemmas/om_fun_1.con".

inline "cic:/CoRN/ftc/COrdLemmas/om_fun_2a.con".

inline "cic:/CoRN/ftc/COrdLemmas/om_fun_2.con".

inline "cic:/CoRN/ftc/COrdLemmas/om_fun_3a.con".

inline "cic:/CoRN/ftc/COrdLemmas/om_fun_3b.con".

inline "cic:/CoRN/ftc/COrdLemmas/om_fun_4a.con".

inline "cic:/CoRN/ftc/COrdLemmas/om_fun_4b.con".

inline "cic:/CoRN/ftc/COrdLemmas/om_fun_4c.con".

inline "cic:/CoRN/ftc/COrdLemmas/om_fun_4d.con".

(* begin hide *)

alias id "f" = "cic:/CoRN/ftc/COrdLemmas/Lemmas/f.var".

alias id "f0" = "cic:/CoRN/ftc/COrdLemmas/Lemmas/f0.var".

alias id "f_mon" = "cic:/CoRN/ftc/COrdLemmas/Lemmas/f_mon.var".

alias id "h" = "cic:/CoRN/ftc/COrdLemmas/Lemmas/h.var".

(* end hide *)

(*#* ** Summations
Also, some technical stuff on sums.  The first lemma relates two
different kinds of sums; the other two ones are variations, where the
structure of the arguments is analyzed in more detail.
*)

(* begin show *)

inline "cic:/CoRN/ftc/COrdLemmas/Sumx_Sum_Sum
 (* end show *)
 (* begin hide *).con".

(* end hide *)

(* begin show *)

inline "cic:/CoRN/ftc/COrdLemmas/str_Sumx_Sum_Sum
 (* end show *)
 (* begin hide *).con".

(* UNEXPORTED
End Lemmas
*)

(* UNEXPORTED
Section More_Lemmas
*)

inline "cic:/CoRN/ftc/COrdLemmas/More_Lemmas/f'.con" "More_Lemmas__".

(* end hide *)

alias id "F" = "cic:/CoRN/ftc/COrdLemmas/More_Lemmas/F.var".

(* begin show *)

inline "cic:/CoRN/ftc/COrdLemmas/str_Sumx_Sum_Sum'
 (* end show *)
 (* begin hide *).con".

(* end hide *)

(* UNEXPORTED
End More_Lemmas
*)

