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

set "baseuri" "cic:/matita/CoRN-Decl/reals/Bridges_LUB".

include "CoRN.ma".

(* begin hide *)

(* file        : least_upper_bound_principle.v                     *)

(* version     : 1.50 -	03/05/2001                                 *)

(* version     : 1.00 - 27/02/2001                                 *)

(* author      : Milad Niqui                                       *)

(* language    : coq 7.0beta26feb                                  *)

(* dependency  : iso_CReals.v , Expon.v                            *)

(* description : proof of the Bridges' least upper bound principle *)

include "reals/iso_CReals.ma".

include "algebra/Expon.ma".

(* UNEXPORTED
Section LUBP
*)

alias id "R1" = "cic:/CoRN/reals/Bridges_LUB/LUBP/R1.var".

(* SUBSECTION ON GENRAL DEFINITIONS *)

(* UNEXPORTED
Section lub_definitions
*)

alias id "OF" = "cic:/CoRN/reals/Bridges_LUB/LUBP/lub_definitions/OF.var".

alias id "SS" = "cic:/CoRN/reals/Bridges_LUB/LUBP/lub_definitions/SS.var".

inline "cic:/CoRN/reals/Bridges_LUB/member.con".

inline "cic:/CoRN/reals/Bridges_LUB/Pmember.con".

inline "cic:/CoRN/reals/Bridges_LUB/is_upper_bound.con".

inline "cic:/CoRN/reals/Bridges_LUB/l_u_b.con".

inline "cic:/CoRN/reals/Bridges_LUB/supremum.con".

inline "cic:/CoRN/reals/Bridges_LUB/Psupremum.con".

(* the following definitions are not used in *)

(* this file but later we will need them     *)

inline "cic:/CoRN/reals/Bridges_LUB/is_lower_bound.con".

inline "cic:/CoRN/reals/Bridges_LUB/g_l_b.con".

inline "cic:/CoRN/reals/Bridges_LUB/infimum.con".

inline "cic:/CoRN/reals/Bridges_LUB/Pinfimum.con".

(* UNEXPORTED
End lub_definitions
*)

(* MAIN SECTION *)

(* UNEXPORTED
Section upper_bound_sequence
*)

alias id "A" = "cic:/CoRN/reals/Bridges_LUB/LUBP/upper_bound_sequence/A.var".

alias id "is_inhabitted" = "cic:/CoRN/reals/Bridges_LUB/LUBP/upper_bound_sequence/is_inhabitted.var".

alias id "bounded_above" = "cic:/CoRN/reals/Bridges_LUB/LUBP/upper_bound_sequence/bounded_above.var".

alias id "located" = "cic:/CoRN/reals/Bridges_LUB/LUBP/upper_bound_sequence/located.var".

inline "cic:/CoRN/reals/Bridges_LUB/LUBP/upper_bound_sequence/s.con" "LUBP__upper_bound_sequence__".

inline "cic:/CoRN/reals/Bridges_LUB/LUBP/upper_bound_sequence/Ps.con" "LUBP__upper_bound_sequence__".

inline "cic:/CoRN/reals/Bridges_LUB/LUBP/upper_bound_sequence/b0.con" "LUBP__upper_bound_sequence__".

inline "cic:/CoRN/reals/Bridges_LUB/LUBP/upper_bound_sequence/Pb0.con" "LUBP__upper_bound_sequence__".

inline "cic:/CoRN/reals/Bridges_LUB/b0_is_upper_bound.con".

inline "cic:/CoRN/reals/Bridges_LUB/s_inhabits_A.con".

inline "cic:/CoRN/reals/Bridges_LUB/LUBP/upper_bound_sequence/dstart_l.con" "LUBP__upper_bound_sequence__".

inline "cic:/CoRN/reals/Bridges_LUB/LUBP/upper_bound_sequence/dstart_r.con" "LUBP__upper_bound_sequence__".

inline "cic:/CoRN/reals/Bridges_LUB/dl_less_dr.con".

inline "cic:/CoRN/reals/Bridges_LUB/shrink23d.con".

inline "cic:/CoRN/reals/Bridges_LUB/shrink13d.con".

inline "cic:/CoRN/reals/Bridges_LUB/shrink24d.con".

inline "cic:/CoRN/reals/Bridges_LUB/Real_Interval.con".

inline "cic:/CoRN/reals/Bridges_LUB/dcotrans_analyze.con".

inline "cic:/CoRN/reals/Bridges_LUB/dcotrans_analyze_strong.con".

(* NOTATION
Notation "( p , q )" := (pairT p q).
*)

inline "cic:/CoRN/reals/Bridges_LUB/dif_cotrans.con".

inline "cic:/CoRN/reals/Bridges_LUB/dif_cotrans_strong.con".

inline "cic:/CoRN/reals/Bridges_LUB/dIntrvl.con".

inline "cic:/CoRN/reals/Bridges_LUB/LUBP/upper_bound_sequence/U.con" "LUBP__upper_bound_sequence__".

inline "cic:/CoRN/reals/Bridges_LUB/LUBP/upper_bound_sequence/V.con" "LUBP__upper_bound_sequence__".

inline "cic:/CoRN/reals/Bridges_LUB/LUBP/upper_bound_sequence/W.con" "LUBP__upper_bound_sequence__".

inline "cic:/CoRN/reals/Bridges_LUB/delta_dIntrvl.con".

inline "cic:/CoRN/reals/Bridges_LUB/Length_dIntrvl.con".

inline "cic:/CoRN/reals/Bridges_LUB/dIntrvl_inside_l_n.con".

inline "cic:/CoRN/reals/Bridges_LUB/dIntrvl_inside_r_n.con".

inline "cic:/CoRN/reals/Bridges_LUB/V_increase.con".

inline "cic:/CoRN/reals/Bridges_LUB/W_decrease.con".

inline "cic:/CoRN/reals/Bridges_LUB/U_m_n_V.con".

inline "cic:/CoRN/reals/Bridges_LUB/U_m_n_W.con".

(*  These lemma are *very* similar to those in  *)

(*  Cauchy_rationals_approach_reals.v           *)

inline "cic:/CoRN/reals/Bridges_LUB/a_familiar_simple_inequality.con".

inline "cic:/CoRN/reals/Bridges_LUB/U_conversion_rate2.con".

inline "cic:/CoRN/reals/Bridges_LUB/CS_seq_U.con".

inline "cic:/CoRN/reals/Bridges_LUB/U_as_CauchySeq.con".

inline "cic:/CoRN/reals/Bridges_LUB/LUBP/upper_bound_sequence/B.con" "LUBP__upper_bound_sequence__".

inline "cic:/CoRN/reals/Bridges_LUB/U_minus_V.con".

inline "cic:/CoRN/reals/Bridges_LUB/U_minus_W.con".

inline "cic:/CoRN/reals/Bridges_LUB/U_V_upper.con".

inline "cic:/CoRN/reals/Bridges_LUB/U_W_lower.con".

inline "cic:/CoRN/reals/Bridges_LUB/AbsSmall_U_V.con".

inline "cic:/CoRN/reals/Bridges_LUB/AbsSmall_U_W.con".

(* Two properties of exponentiation in COrdFields *)

inline "cic:/CoRN/reals/Bridges_LUB/nexp_resp_great_One.con".

inline "cic:/CoRN/reals/Bridges_LUB/very_weak_binomial.con".

(* A consequence of Archimedean property -         *)

(* the every basis of definition of e=lim(1+1/n)^n *)

inline "cic:/CoRN/reals/Bridges_LUB/nexp_resp_Two.con".

inline "cic:/CoRN/reals/Bridges_LUB/twisted_archimedean.con".

inline "cic:/CoRN/reals/Bridges_LUB/B_limit_V.con".

inline "cic:/CoRN/reals/Bridges_LUB/B_limit_W.con".

inline "cic:/CoRN/reals/Bridges_LUB/W_n_is_upper.con".

inline "cic:/CoRN/reals/Bridges_LUB/A_bounds_V_n.con".

inline "cic:/CoRN/reals/Bridges_LUB/cauchy_gives_lub.con".

(* UNEXPORTED
End upper_bound_sequence
*)

(* UNEXPORTED
End LUBP
*)

(* end hide *)

