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

set "baseuri" "cic:/matita/CoRN-Decl/algebra/COrdFields".

include "CoRN.ma".

(* $Id: COrdFields.v,v 1.6 2004/04/23 10:00:52 lcf Exp $ *)

(*#* printing [<] %\ensuremath<% #&lt;# *)

(*#* printing [<=] %\ensuremath{\leq}% #&le;# *)

(*#* printing [>] %\ensuremath>% #&gt;# *)

(*#* printing OneNZ %\ensuremath{\mathbf1}% #1# *)

(*#* printing TwoNZ %\ensuremath{\mathbf2}% #2# *)

(*#* printing ThreeNZ %\ensuremath{\mathbf3}% #3# *)

(*#* printing FourNZ %\ensuremath{\mathbf4}% #4# *)

(*#* printing SixNZ %\ensuremath{\mathbf6}% #6# *)

(*#* printing EightNZ %\ensuremath{\mathbf8}% #8# *)

(*#* printing NineNZ %\ensuremath{\mathbf9}% #9# *)

(*#* printing TwelveNZ %\ensuremath{\mathbf{12}}% #12# *)

(*#* printing SixteenNZ %\ensuremath{\mathbf{16}}% #16# *)

(*#* printing EighteenNZ %\ensuremath{\mathbf{18}}% #18# *)

(*#* printing TwentyFourNZ %\ensuremath{\mathbf{24}}% #24# *)

(*#* printing FortyEightNZ %\ensuremath{\mathbf{48}}% #48# *)

include "tactics/FieldReflection.ma".

(* ORDERED FIELDS *)

(*#*
* Ordered Fields
** Definition of the notion of ordered field
*)

(* Begin_SpecReals *)

inline "cic:/CoRN/algebra/COrdFields/strictorder.ind".

(* UNEXPORTED
Implicit Arguments strictorder [A].
*)

(* UNEXPORTED
Implicit Arguments Build_strictorder [A R].
*)

(* UNEXPORTED
Implicit Arguments so_trans [A R].
*)

(* UNEXPORTED
Implicit Arguments so_asym [A R].
*)

inline "cic:/CoRN/algebra/COrdFields/is_COrdField.ind".

inline "cic:/CoRN/algebra/COrdFields/COrdField.ind".

coercion cic:/matita/CoRN-Decl/algebra/COrdFields/cof_crr.con 0 (* compounds *).

(*#*
%\begin{nameconvention}%
In the names of lemmas, [ [<] ] is written as [less] and "[Zero [<] ]"
is written as [pos].
%\end{nameconvention}%
*)

(* UNEXPORTED
Implicit Arguments cof_less [c].
*)

(* NOTATION
Infix "[<]" := cof_less (at level 70, no associativity).
*)

inline "cic:/CoRN/algebra/COrdFields/greater.con".

(* UNEXPORTED
Implicit Arguments greater [F].
*)

(* NOTATION
Infix "[>]" := greater (at level 70, no associativity).
*)

(* End_SpecReals *)

(*#*
Less or equal is defined as ``not greater than''.
*)

inline "cic:/CoRN/algebra/COrdFields/leEq.con".

(*#*
%\begin{nameconvention}%
In the names of lemmas, [ [<=] ] is written as [leEq] and
[Zero [<=] ] is written as [nonneg].
%\end{nameconvention}%
*)

(* UNEXPORTED
Implicit Arguments leEq [F].
*)

(* NOTATION
Infix "[<=]" := leEq (at level 70, no associativity).
*)

(* UNEXPORTED
Section COrdField_axioms
*)

(*#*
** Ordered field axioms
%\begin{convention}%
Let [F] be a field.
%\end{convention}%
*)

alias id "F" = "cic:/CoRN/algebra/COrdFields/COrdField_axioms/F.var".

inline "cic:/CoRN/algebra/COrdFields/COrdField_is_COrdField.con".

inline "cic:/CoRN/algebra/COrdFields/less_strorder.con".

inline "cic:/CoRN/algebra/COrdFields/less_transitive_unfolded.con".

inline "cic:/CoRN/algebra/COrdFields/less_antisymmetric_unfolded.con".

inline "cic:/CoRN/algebra/COrdFields/less_irreflexive.con".

inline "cic:/CoRN/algebra/COrdFields/less_irreflexive_unfolded.con".

inline "cic:/CoRN/algebra/COrdFields/plus_resp_less_rht.con".

inline "cic:/CoRN/algebra/COrdFields/mult_resp_pos.con".

inline "cic:/CoRN/algebra/COrdFields/less_conf_ap.con".

inline "cic:/CoRN/algebra/COrdFields/less_wdr.con".

inline "cic:/CoRN/algebra/COrdFields/less_wdl.con".

(* UNEXPORTED
End COrdField_axioms
*)

(* UNEXPORTED
Declare Left Step less_wdl.
*)

(* UNEXPORTED
Declare Right Step less_wdr.
*)

(* UNEXPORTED
Section OrdField_basics
*)

(*#*
** Basics
*)

(*#*
%\begin{convention}%
Let in the rest of this section (and all subsections)
[R] be an ordered field
%\end{convention}%
*)

alias id "R" = "cic:/CoRN/algebra/COrdFields/OrdField_basics/R.var".

inline "cic:/CoRN/algebra/COrdFields/less_imp_ap.con".

inline "cic:/CoRN/algebra/COrdFields/Greater_imp_ap.con".

inline "cic:/CoRN/algebra/COrdFields/ap_imp_less.con".

(*#*
Now properties which can be derived.
*)

inline "cic:/CoRN/algebra/COrdFields/less_cotransitive.con".

inline "cic:/CoRN/algebra/COrdFields/less_cotransitive_unfolded.con".

inline "cic:/CoRN/algebra/COrdFields/pos_ap_zero.con".

(* Main characterization of less *)

inline "cic:/CoRN/algebra/COrdFields/leEq_not_eq.con".

(* UNEXPORTED
End OrdField_basics
*)

(*#**********************************)

(* UNEXPORTED
Section Basic_Properties_of_leEq
*)

(*#**********************************)

(*#* ** Basic properties of [ [<=] ]
*)

alias id "R" = "cic:/CoRN/algebra/COrdFields/Basic_Properties_of_leEq/R.var".

inline "cic:/CoRN/algebra/COrdFields/leEq_wdr.con".

inline "cic:/CoRN/algebra/COrdFields/leEq_wdl.con".

inline "cic:/CoRN/algebra/COrdFields/leEq_reflexive.con".

(* UNEXPORTED
Declare Left Step leEq_wdl.
*)

(* UNEXPORTED
Declare Right Step leEq_wdr.
*)

inline "cic:/CoRN/algebra/COrdFields/eq_imp_leEq.con".

inline "cic:/CoRN/algebra/COrdFields/leEq_imp_eq.con".

inline "cic:/CoRN/algebra/COrdFields/lt_equiv_imp_eq.con".

inline "cic:/CoRN/algebra/COrdFields/less_leEq_trans.con".

inline "cic:/CoRN/algebra/COrdFields/leEq_less_trans.con".

inline "cic:/CoRN/algebra/COrdFields/leEq_transitive.con".

inline "cic:/CoRN/algebra/COrdFields/less_leEq.con".

(* UNEXPORTED
End Basic_Properties_of_leEq
*)

(* UNEXPORTED
Declare Left Step leEq_wdl.
*)

(* UNEXPORTED
Declare Right Step leEq_wdr.
*)

(* UNEXPORTED
Section infinity_of_cordfields
*)

(*#*
** Infinity of ordered fields

In an ordered field we have that [One[+]One] and
[One[+]One[+]One] and so on are all apart from zero.
We first show this, so that we can define [TwoNZ], [ThreeNZ]
and so on. These are elements of [NonZeros], so that we can write
e.g.%\% [x[/]TwoNZ].
*)

alias id "R" = "cic:/CoRN/algebra/COrdFields/infinity_of_cordfields/R.var".

inline "cic:/CoRN/algebra/COrdFields/pos_one.con".

inline "cic:/CoRN/algebra/COrdFields/nring_less_succ.con".

inline "cic:/CoRN/algebra/COrdFields/nring_less.con".

inline "cic:/CoRN/algebra/COrdFields/nring_leEq.con".

inline "cic:/CoRN/algebra/COrdFields/nring_apart.con".

inline "cic:/CoRN/algebra/COrdFields/nring_ap_zero.con".

inline "cic:/CoRN/algebra/COrdFields/nring_ap_zero'.con".

inline "cic:/CoRN/algebra/COrdFields/nring_ap_zero_imp.con".

inline "cic:/CoRN/algebra/COrdFields/Snring.con".

include "tactics/Transparent_algebra.ma".

inline "cic:/CoRN/algebra/COrdFields/pos_Snring.con".

inline "cic:/CoRN/algebra/COrdFields/nringS_ap_zero.con".

inline "cic:/CoRN/algebra/COrdFields/nring_fac_ap_zero.con".

include "tactics/Opaque_algebra.ma".

(* UNEXPORTED
Section up_to_four
*)

(*#*
*** Properties of one up to four
%\begin{nameconvention}%
In the names of lemmas, we denote the numbers 0,1,2,3,4 and so on, by
[zero], [one], [two] etc.
%\end{nameconvention}%
*)

inline "cic:/CoRN/algebra/COrdFields/less_plusOne.con".

inline "cic:/CoRN/algebra/COrdFields/zero_lt_posplus1.con".

inline "cic:/CoRN/algebra/COrdFields/plus_one_ext_less.con".

inline "cic:/CoRN/algebra/COrdFields/one_less_two.con".

inline "cic:/CoRN/algebra/COrdFields/two_less_three.con".

inline "cic:/CoRN/algebra/COrdFields/three_less_four.con".

inline "cic:/CoRN/algebra/COrdFields/pos_two.con".

inline "cic:/CoRN/algebra/COrdFields/one_less_three.con".

inline "cic:/CoRN/algebra/COrdFields/two_less_four.con".

inline "cic:/CoRN/algebra/COrdFields/pos_three.con".

inline "cic:/CoRN/algebra/COrdFields/one_less_four.con".

inline "cic:/CoRN/algebra/COrdFields/pos_four.con".

inline "cic:/CoRN/algebra/COrdFields/two_ap_zero.con".

inline "cic:/CoRN/algebra/COrdFields/three_ap_zero.con".

inline "cic:/CoRN/algebra/COrdFields/four_ap_zero.con".

(* UNEXPORTED
End up_to_four
*)

(* UNEXPORTED
Section More_than_four
*)

(*#* *** Properties of some other numbers *)

inline "cic:/CoRN/algebra/COrdFields/pos_six.con".

inline "cic:/CoRN/algebra/COrdFields/pos_eight.con".

inline "cic:/CoRN/algebra/COrdFields/pos_nine.con".

inline "cic:/CoRN/algebra/COrdFields/pos_twelve.con".

inline "cic:/CoRN/algebra/COrdFields/pos_sixteen.con".

inline "cic:/CoRN/algebra/COrdFields/pos_eighteen.con".

inline "cic:/CoRN/algebra/COrdFields/pos_twentyfour.con".

inline "cic:/CoRN/algebra/COrdFields/pos_fortyeight.con".

inline "cic:/CoRN/algebra/COrdFields/six_ap_zero.con".

inline "cic:/CoRN/algebra/COrdFields/eight_ap_zero.con".

inline "cic:/CoRN/algebra/COrdFields/nine_ap_zero.con".

inline "cic:/CoRN/algebra/COrdFields/twelve_ap_zero.con".

inline "cic:/CoRN/algebra/COrdFields/sixteen_ap_zero.con".

inline "cic:/CoRN/algebra/COrdFields/eighteen_ap_zero.con".

inline "cic:/CoRN/algebra/COrdFields/twentyfour_ap_zero.con".

inline "cic:/CoRN/algebra/COrdFields/fortyeight_ap_zero.con".

(* UNEXPORTED
End More_than_four
*)

(* UNEXPORTED
End infinity_of_cordfields
*)

(* UNEXPORTED
Declare Left Step leEq_wdl.
*)

(* UNEXPORTED
Declare Right Step leEq_wdr.
*)

(* NOTATION
Notation " x [/]OneNZ" := (x[/] One[//]ring_non_triv _) (at level 20).
*)

(* NOTATION
Notation " x [/]TwoNZ" := (x[/] Two[//]two_ap_zero _) (at level 20).
*)

(* NOTATION
Notation " x [/]ThreeNZ" := (x[/] Three[//]three_ap_zero _) (at level 20).
*)

(* NOTATION
Notation " x [/]FourNZ" := (x[/] Four[//]four_ap_zero _) (at level 20).
*)

(* NOTATION
Notation " x [/]SixNZ" := (x[/] Six[//]six_ap_zero _) (at level 20).
*)

(* NOTATION
Notation " x [/]EightNZ" := (x[/] Eight[//]eight_ap_zero _) (at level 20).
*)

(* NOTATION
Notation " x [/]NineNZ" := (x[/] Nine[//]nine_ap_zero _) (at level 20).
*)

(* NOTATION
Notation " x [/]TwelveNZ" := (x[/] Twelve[//]twelve_ap_zero _) (at level 20).
*)

(* NOTATION
Notation " x [/]SixteenNZ" := (x[/] Sixteen[//]sixteen_ap_zero _) (at level 20).
*)

(* NOTATION
Notation " x [/]EighteenNZ" := (x[/] Eighteen[//]eighteen_ap_zero _) (at level 20).
*)

(* NOTATION
Notation " x [/]TwentyFourNZ" := (x[/] TwentyFour[//]twentyfour_ap_zero _) (at level 20).
*)

(* NOTATION
Notation " x [/]FortyEightNZ" := (x[/] FortyEight[//]fortyeight_ap_zero _) (at level 20).
*)

(* UNEXPORTED
Section consequences_of_infinity
*)

(*#*
*** Consequences of infinity
*)

alias id "F" = "cic:/CoRN/algebra/COrdFields/consequences_of_infinity/F.var".

inline "cic:/CoRN/algebra/COrdFields/square_eq.con".

(*#*
Ordered fields have characteristic zero.
*)

inline "cic:/CoRN/algebra/COrdFields/char0_OrdField.con".

(* UNEXPORTED
End consequences_of_infinity
*)

(*#**********************************)

(* UNEXPORTED
Section Properties_of_Ordering
*)

(*#**********************************)

(*#*
** Properties of [[<]]
*)

alias id "R" = "cic:/CoRN/algebra/COrdFields/Properties_of_Ordering/R.var".

(*#*
We do not use a special predicate for positivity,
(e.g.%\% [PosP]), but just write [Zero [<] x].
Reasons: it is more natural; in ordinary mathematics we also write [Zero [<] x]
(or [x [>] Zero]).

*)

(* UNEXPORTED
Section addition
*)

(*#*
*** Addition and subtraction%\label{section:less_plus_minus}%

*)

inline "cic:/CoRN/algebra/COrdFields/plus_resp_less_lft.con".

inline "cic:/CoRN/algebra/COrdFields/inv_resp_less.con".

(* UNEXPORTED
Transparent cg_minus.
*)

inline "cic:/CoRN/algebra/COrdFields/minus_resp_less.con".

(* UNEXPORTED
Transparent cg_minus.
*)

inline "cic:/CoRN/algebra/COrdFields/minus_resp_less_rht.con".

inline "cic:/CoRN/algebra/COrdFields/plus_resp_less_both.con".

(*#*
For versions of [plus_resp_less_both] where one [ [<] ] in the
assumption is replaced by [ [<=] ]%, see
Section~\ref{section:leEq-plus-minus}%.

Cancellation laws
*)

inline "cic:/CoRN/algebra/COrdFields/plus_cancel_less.con".

inline "cic:/CoRN/algebra/COrdFields/inv_cancel_less.con".

(*#*

Lemmas where an operation is transformed into the inverse operation on
the other side of an inequality are called laws for shifting.
%\begin{nameconvention}%
The names of laws for shifting start with [shift_], and then come
the operation and the inequality, in the order in which they occur in the
conclusion.
If the shifted operand changes sides w.r.t.%\% the operation and its inverse,
the name gets a prime.
%\end{nameconvention}%

It would be nicer to write the laws for shifting as bi-implications,
However, it is impractical to use these in
Coq%(see the Coq shortcoming in Section~\ref{section:setoid-basics})%.
*)

inline "cic:/CoRN/algebra/COrdFields/shift_less_plus.con".

inline "cic:/CoRN/algebra/COrdFields/shift_less_plus'.con".

inline "cic:/CoRN/algebra/COrdFields/shift_less_minus.con".

inline "cic:/CoRN/algebra/COrdFields/shift_less_minus'.con".

inline "cic:/CoRN/algebra/COrdFields/shift_plus_less.con".

inline "cic:/CoRN/algebra/COrdFields/shift_plus_less'.con".

inline "cic:/CoRN/algebra/COrdFields/shift_minus_less.con".

inline "cic:/CoRN/algebra/COrdFields/shift_minus_less'.con".

(*#*
Some special cases of laws for shifting.
*)

inline "cic:/CoRN/algebra/COrdFields/shift_zero_less_minus.con".

inline "cic:/CoRN/algebra/COrdFields/shift_zero_less_minus'.con".

inline "cic:/CoRN/algebra/COrdFields/qltone.con".

(* UNEXPORTED
End addition
*)

(* UNEXPORTED
Section multiplication
*)

(*#*
*** Multiplication and division
By Convention%~\ref{convention:div-form}%
in CFields% (Section~\ref{section:fields})%, we often have redundant premises
in lemmas. E.g.%\% the informal statement
``for all [x,y : R] with  [Zero [<] x] and [Zero [<] y]
we have [Zero [<] y[/]x]''
is formalized as follows.
[[
forall (x y : R) x_, (Zero [<] x) -> (Zero [<] y) -> (Zero [<] y[/]x[//]H)
]]
We do this to keep it easy to use such lemmas.

*)

inline "cic:/CoRN/algebra/COrdFields/mult_resp_less.con".

inline "cic:/CoRN/algebra/COrdFields/recip_resp_pos.con".

inline "cic:/CoRN/algebra/COrdFields/div_resp_less_rht.con".

inline "cic:/CoRN/algebra/COrdFields/div_resp_pos.con".

inline "cic:/CoRN/algebra/COrdFields/mult_resp_less_lft.con".

inline "cic:/CoRN/algebra/COrdFields/mult_resp_less_both.con".

inline "cic:/CoRN/algebra/COrdFields/recip_resp_less.con".

inline "cic:/CoRN/algebra/COrdFields/div_resp_less.con".

(*#* Cancellation laws
*)

inline "cic:/CoRN/algebra/COrdFields/mult_cancel_less.con".

(*#*
Laws for shifting

%For namegiving, see the Section~\ref{section:less_plus_minus}
on plus and minus.%
*)

inline "cic:/CoRN/algebra/COrdFields/shift_div_less.con".

inline "cic:/CoRN/algebra/COrdFields/shift_div_less'.con".

inline "cic:/CoRN/algebra/COrdFields/shift_less_div.con".

inline "cic:/CoRN/algebra/COrdFields/shift_less_mult.con".

inline "cic:/CoRN/algebra/COrdFields/shift_less_mult'.con".

inline "cic:/CoRN/algebra/COrdFields/shift_mult_less.con".

(*#* Other properties of multiplication and division
*)

inline "cic:/CoRN/algebra/COrdFields/minusOne_less.con".

inline "cic:/CoRN/algebra/COrdFields/swap_div.con".

inline "cic:/CoRN/algebra/COrdFields/eps_div_less_eps.con".

inline "cic:/CoRN/algebra/COrdFields/pos_div_two.con".

inline "cic:/CoRN/algebra/COrdFields/pos_div_two'.con".

(*
Apply mult_cancel_less with (Two::R).
Apply pos_two.
rstepl eps[+]Zero; rstepr eps[+]eps.
Apply plus_resp_less_lft.
Auto.
Qed.
*)

inline "cic:/CoRN/algebra/COrdFields/pos_div_three.con".

inline "cic:/CoRN/algebra/COrdFields/pos_div_three'.con".

inline "cic:/CoRN/algebra/COrdFields/pos_div_four.con".

inline "cic:/CoRN/algebra/COrdFields/pos_div_four'.con".

inline "cic:/CoRN/algebra/COrdFields/pos_div_six.con".

inline "cic:/CoRN/algebra/COrdFields/pos_div_eight.con".

inline "cic:/CoRN/algebra/COrdFields/pos_div_nine.con".

inline "cic:/CoRN/algebra/COrdFields/pos_div_twelve.con".

inline "cic:/CoRN/algebra/COrdFields/pos_div_sixteen.con".

inline "cic:/CoRN/algebra/COrdFields/pos_div_eighteen.con".

inline "cic:/CoRN/algebra/COrdFields/pos_div_twentyfour.con".

inline "cic:/CoRN/algebra/COrdFields/pos_div_fortyeight.con".

(* UNEXPORTED
End multiplication
*)

(* UNEXPORTED
Section misc
*)

(*#*
*** Miscellaneous properties
*)

inline "cic:/CoRN/algebra/COrdFields/nring_pos.con".

inline "cic:/CoRN/algebra/COrdFields/less_nring.con".

inline "cic:/CoRN/algebra/COrdFields/pos_nring_fac.con".

inline "cic:/CoRN/algebra/COrdFields/Smallest_less_Average.con".

inline "cic:/CoRN/algebra/COrdFields/Average_less_Greatest.con".

inline "cic:/CoRN/algebra/COrdFields/Sum_resp_less.con".

inline "cic:/CoRN/algebra/COrdFields/Sumx_resp_less.con".

inline "cic:/CoRN/algebra/COrdFields/positive_Sum_two.con".

inline "cic:/CoRN/algebra/COrdFields/positive_Sumx.con".

inline "cic:/CoRN/algebra/COrdFields/negative_Sumx.con".

(* UNEXPORTED
End misc
*)

(* UNEXPORTED
End Properties_of_Ordering
*)

