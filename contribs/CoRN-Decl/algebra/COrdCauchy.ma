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

set "baseuri" "cic:/matita/CoRN-Decl/algebra/COrdCauchy".

include "CoRN.ma".

include "algebra/COrdAbs.ma".

(* Begin_SpecReals *)

(* UNEXPORTED
Section OrdField_Cauchy
*)

(*#* **Cauchy sequences
%\begin{convention}% Let [R] be an ordered field.
%\end{convention}%
*)

alias id "R" = "cic:/CoRN/algebra/COrdCauchy/OrdField_Cauchy/R.var".

(* begin hide *)

(* UNEXPORTED
Set Implicit Arguments.
*)

(* UNEXPORTED
Unset Strict Implicit.
*)

(* end hide *)

inline "cic:/CoRN/algebra/COrdCauchy/Cauchy_prop.con".

(* begin hide *)

(* UNEXPORTED
Set Strict Implicit.
*)

(* UNEXPORTED
Unset Implicit Arguments.
*)

(* end hide *)

(* Def. CauchyP, Build_CauchyP *)

(* Should be defined in terms of CauchyP *)

(*#*
Implicit arguments turned off, because Coq makes a mess of it in combination
with the coercions
*)

inline "cic:/CoRN/algebra/COrdCauchy/CauchySeq.ind".

coercion cic:/matita/CoRN-Decl/algebra/COrdCauchy/CS_seq.con 0 (* compounds *).

inline "cic:/CoRN/algebra/COrdCauchy/SeqLimit.con".

(* End_SpecReals *)

(*#*
We now prove that the property of being a Cauchy sequence is preserved
through the usual algebraic operations (addition, subtraction and
multiplication -- and division, provided some additional conditions
hold).

%\begin{convention}% Let [R] be an ordered field.
%\end{convention}%
*)

inline "cic:/CoRN/algebra/COrdCauchy/CS_seq_bounded.con".

inline "cic:/CoRN/algebra/COrdCauchy/CS_seq_const.con".

(*#*
%\begin{convention}% Assume [f] and [g] are Cauchy sequences on [R].
%\end{convention}%
*)

alias id "f" = "cic:/CoRN/algebra/COrdCauchy/OrdField_Cauchy/f.var".

alias id "g" = "cic:/CoRN/algebra/COrdCauchy/OrdField_Cauchy/g.var".

alias id "Hf" = "cic:/CoRN/algebra/COrdCauchy/OrdField_Cauchy/Hf.var".

alias id "Hg" = "cic:/CoRN/algebra/COrdCauchy/OrdField_Cauchy/Hg.var".

inline "cic:/CoRN/algebra/COrdCauchy/CS_seq_plus.con".

inline "cic:/CoRN/algebra/COrdCauchy/CS_seq_inv.con".

inline "cic:/CoRN/algebra/COrdCauchy/CS_seq_mult.con".

(*#*
We now assume that [f] is, from some point onwards, greater than
some positive number.  The sequence of reciprocals is defined as
being constantly one up to that point, and the sequence of
reciprocals from then onwards.

%\begin{convention}%
Let [e] be a postive element of [R] and let [N:nat] be such that from
[N] onwards, [(f n) [#] Zero]
%\end{convention}%
*)

alias id "e" = "cic:/CoRN/algebra/COrdCauchy/OrdField_Cauchy/e.var".

alias id "He" = "cic:/CoRN/algebra/COrdCauchy/OrdField_Cauchy/He.var".

alias id "N" = "cic:/CoRN/algebra/COrdCauchy/OrdField_Cauchy/N.var".

alias id "f_bnd" = "cic:/CoRN/algebra/COrdCauchy/OrdField_Cauchy/f_bnd.var".

inline "cic:/CoRN/algebra/COrdCauchy/CS_seq_recip_def.con".

inline "cic:/CoRN/algebra/COrdCauchy/CS_seq_recip_seq.con".

inline "cic:/CoRN/algebra/COrdCauchy/CS_seq_recip.con".

(* UNEXPORTED
End OrdField_Cauchy
*)

(* UNEXPORTED
Implicit Arguments SeqLimit [R].
*)

(*#*
The following lemma does not require the sequence to be Cauchy, but it fits
well here anyway.
*)

inline "cic:/CoRN/algebra/COrdCauchy/maj_upto_eps.con".

(* UNEXPORTED
Section Mult_AbsSmall
*)

alias id "R" = "cic:/CoRN/algebra/COrdCauchy/Mult_AbsSmall/R.var".

(*#*
** [AbsSmall] revisited
%\begin{convention}% Let [R] be an ordered field.
%\end{convention}%
*)

inline "cic:/CoRN/algebra/COrdCauchy/mult_AbsSmall'_rht.con".

inline "cic:/CoRN/algebra/COrdCauchy/mult_AbsSmall_rht.con".

inline "cic:/CoRN/algebra/COrdCauchy/mult_AbsSmall_lft.con".

inline "cic:/CoRN/algebra/COrdCauchy/mult_AbsSmall.con".

(* UNEXPORTED
End Mult_AbsSmall
*)

(* UNEXPORTED
Section Mult_Continuous
*)

alias id "R" = "cic:/CoRN/algebra/COrdCauchy/Mult_Continuous/R.var".

(*#*
** Multiplication is continuous
%\begin{convention}% Let [R] be an ordered field.
%\end{convention}%
*)

inline "cic:/CoRN/algebra/COrdCauchy/smaller.con".

inline "cic:/CoRN/algebra/COrdCauchy/estimate_abs.con".

inline "cic:/CoRN/algebra/COrdCauchy/mult_contin.con".

(*#* Addition is also continuous. *)

inline "cic:/CoRN/algebra/COrdCauchy/plus_contin.con".

(* UNEXPORTED
End Mult_Continuous
*)

(* UNEXPORTED
Section Monotonous_functions
*)

(*#*
** Monotonous Functions

Finally, we study several properties of monotonous functions and
characterize them in some way.

%\begin{convention}% Let [R] be an ordered field.
%\end{convention}%
*)

alias id "R" = "cic:/CoRN/algebra/COrdCauchy/Monotonous_functions/R.var".

(*#*
We begin by characterizing the preservation of less (less or equal)
in terms of preservation of less or equal (less).
*)

inline "cic:/CoRN/algebra/COrdCauchy/resp_less_char'.con".

inline "cic:/CoRN/algebra/COrdCauchy/resp_less_char.con".

inline "cic:/CoRN/algebra/COrdCauchy/resp_leEq_char'.con".

inline "cic:/CoRN/algebra/COrdCauchy/resp_leEq_char.con".

(*#*
Next, we see different characterizations of monotonous functions from
some subset of the natural numbers into [R].  Mainly, these
amount (for different types of functions) to proving that a function
is monotonous iff [f(i) [<] f(i+1)] for every [i].

Also, strictly monotonous functions are injective.
*)

inline "cic:/CoRN/algebra/COrdCauchy/local_mon_imp_mon.con".

inline "cic:/CoRN/algebra/COrdCauchy/local_mon_imp_mon'.con".

inline "cic:/CoRN/algebra/COrdCauchy/local_mon'_imp_mon'.con".

inline "cic:/CoRN/algebra/COrdCauchy/mon_imp_mon'.con".

inline "cic:/CoRN/algebra/COrdCauchy/mon_imp_inj.con".

inline "cic:/CoRN/algebra/COrdCauchy/local_mon_imp_mon_lt.con".

inline "cic:/CoRN/algebra/COrdCauchy/local_mon_imp_mon'_lt.con".

inline "cic:/CoRN/algebra/COrdCauchy/local_mon'_imp_mon'_lt.con".

inline "cic:/CoRN/algebra/COrdCauchy/local_mon'_imp_mon'2_lt.con".

inline "cic:/CoRN/algebra/COrdCauchy/mon_imp_mon'_lt.con".

inline "cic:/CoRN/algebra/COrdCauchy/mon_imp_inj_lt.con".

inline "cic:/CoRN/algebra/COrdCauchy/local_mon_imp_mon_le.con".

inline "cic:/CoRN/algebra/COrdCauchy/local_mon_imp_mon'_le.con".

inline "cic:/CoRN/algebra/COrdCauchy/local_mon'_imp_mon'_le.con".

inline "cic:/CoRN/algebra/COrdCauchy/local_mon'_imp_mon'2_le.con".

inline "cic:/CoRN/algebra/COrdCauchy/mon_imp_mon'_le.con".

inline "cic:/CoRN/algebra/COrdCauchy/mon_imp_inj_le.con".

(*#*
A similar result for %{\em %partial%}% functions.
*)

inline "cic:/CoRN/algebra/COrdCauchy/part_mon_imp_mon'.con".

(* UNEXPORTED
End Monotonous_functions
*)

