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

set "baseuri" "cic:/matita/CoRN-Decl/fta/CC_Props".

include "CoRN.ma".

(* $Id: CC_Props.v,v 1.3 2004/04/23 10:00:56 lcf Exp $ *)

include "complex/AbsCC.ma".

(*#* * More properties of complex numbers
** Sequences and limits *)

(* UNEXPORTED
Hint Resolve AbsIR_sqrt_sqr: algebra.
*)

inline "cic:/CoRN/fta/CC_Props/absCC_absIR_re.con".

inline "cic:/CoRN/fta/CC_Props/absCC_absIR_im.con".

inline "cic:/CoRN/fta/CC_Props/seq_re.con".

inline "cic:/CoRN/fta/CC_Props/seq_im.con".

inline "cic:/CoRN/fta/CC_Props/CC_Cauchy_prop.con".

inline "cic:/CoRN/fta/CC_Props/CC_CauchySeq.ind".

coercion cic:/matita/CoRN-Decl/fta/CC_Props/CC_seq.con 0 (* compounds *).

inline "cic:/CoRN/fta/CC_Props/re_is_Cauchy.con".

inline "cic:/CoRN/fta/CC_Props/im_is_Cauchy.con".

inline "cic:/CoRN/fta/CC_Props/CC_Cauchy2re.con".

inline "cic:/CoRN/fta/CC_Props/CC_Cauchy2im.con".

inline "cic:/CoRN/fta/CC_Props/LimCC.con".

inline "cic:/CoRN/fta/CC_Props/CC_SeqLimit.con".

inline "cic:/CoRN/fta/CC_Props/AbsSmall_sqr.con".

inline "cic:/CoRN/fta/CC_Props/AbsSmall_AbsCC.con".

inline "cic:/CoRN/fta/CC_Props/LimCC_is_lim.con".

inline "cic:/CoRN/fta/CC_Props/CC_SeqLimit_uniq.con".

inline "cic:/CoRN/fta/CC_Props/CC_SeqLimit_unq.con".

(*#* ** Continuity for [CC]
*)

(* UNEXPORTED
Section Continuity_for_CC
*)

(*#*
%\begin{convention}% Let [f : CC->CC].
%\end{convention}%
*)

alias id "f" = "cic:/CoRN/fta/CC_Props/Continuity_for_CC/f.var".

(* (CSetoid_un_op CC). *)

inline "cic:/CoRN/fta/CC_Props/CCfunLim.con".

inline "cic:/CoRN/fta/CC_Props/CCcontinAt.con".

inline "cic:/CoRN/fta/CC_Props/CCcontin.con".

inline "cic:/CoRN/fta/CC_Props/CCfunLim_SeqLimit.con".

inline "cic:/CoRN/fta/CC_Props/f_seq.con".

inline "cic:/CoRN/fta/CC_Props/poly_pres_lim.con".

(* UNEXPORTED
End Continuity_for_CC
*)

inline "cic:/CoRN/fta/CC_Props/seq_yields_zero.con".

