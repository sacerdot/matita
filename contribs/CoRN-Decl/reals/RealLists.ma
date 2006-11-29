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

set "baseuri" "cic:/matita/CoRN-Decl/reals/RealLists".

include "CoRN.ma".

(* $Id: RealLists.v,v 1.4 2004/04/23 10:01:05 lcf Exp $ *)

include "reals/CReals1.ma".

(* UNEXPORTED
Section Lists
*)

(*#* * Lists of Real Numbers

In some contexts we will need to work with nested existential quantified formulas of the form $\exists_{n\in\NN}\exists_{x_1,\ldots,x_n}P(x_1,\ldots,x_n)$#exists n exists x1,...,xn P(x1,..,xn)#.  One way of formalizing this kind of statement is through quantifying over lists.  In this file we provide some tools for manipulating lists.

Notice that some of the properties listed below only make sense in the context within which we are working.  Unlike in the other lemma files, no care has been taken here to state the lemmas in their most general form, as that would make them very unpractical to use.

%\bigskip%

We start by defining maximum and minimum of lists of reals and two membership predicates. The value of these functions for the empty list is arbitrarily set to 0, but it will be irrelevant, as we will never work with empty lists.
*)

inline "cic:/CoRN/reals/RealLists/maxlist.con".

inline "cic:/CoRN/reals/RealLists/minlist.con".

inline "cic:/CoRN/reals/RealLists/member.con".

(*#*
Sometimes the length of the list has to be restricted; the next definition provides an easy way to do that. *)

inline "cic:/CoRN/reals/RealLists/length_leEq.con".

(*#* Length is preserved by mapping. *)

(* UNEXPORTED
Implicit Arguments map [A B].
*)

inline "cic:/CoRN/reals/RealLists/map_pres_length.con".

(*#* 
Often we want to map partial functions through a list; this next operator provides a way to do that, and is proved to be correct. *)

(* UNEXPORTED
Implicit Arguments cons [A].
*)

inline "cic:/CoRN/reals/RealLists/map2.con".

inline "cic:/CoRN/reals/RealLists/map2_wd.con".

inline "cic:/CoRN/reals/RealLists/map2_pres_member.con".

(*#*
As [maxlist] and [minlist] are generalizations of [Max] and [Min] to finite sets of real numbers, they have the expected properties: *)

inline "cic:/CoRN/reals/RealLists/maxlist_greater.con".

(* begin hide *)

inline "cic:/CoRN/reals/RealLists/Lists/maxlist_aux.con" "Lists__".

(* end hide *)

inline "cic:/CoRN/reals/RealLists/maxlist_leEq_eps.con".

inline "cic:/CoRN/reals/RealLists/maxlist_less.con".

inline "cic:/CoRN/reals/RealLists/maxlist_leEq.con".

inline "cic:/CoRN/reals/RealLists/minlist_smaller.con".

(* begin hide *)

inline "cic:/CoRN/reals/RealLists/Lists/minlist_aux.con" "Lists__".

(* end hide *)

inline "cic:/CoRN/reals/RealLists/minlist_leEq_eps.con".

inline "cic:/CoRN/reals/RealLists/less_minlist.con".

inline "cic:/CoRN/reals/RealLists/leEq_minlist.con".

(* UNEXPORTED
End Lists
*)

