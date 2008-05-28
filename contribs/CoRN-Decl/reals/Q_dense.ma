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

set "baseuri" "cic:/matita/CoRN-Decl/reals/Q_dense".

include "CoRN.ma".

(* begin hide *)

include "reals/Q_in_CReals.ma".

(*#***** Opaque_algebra.v will be loaded in line 151 ******)

inline "cic:/CoRN/reals/Q_dense/or_not_and.con".

(* UNEXPORTED
Section Interval_definition
*)

alias id "OF" = "cic:/CoRN/reals/Q_dense/Interval_definition/OF.var".

inline "cic:/CoRN/reals/Q_dense/Interval.ind".

coercion cic:/matita/CoRN-Decl/reals/Q_dense/pair_crr.con 0 (* compounds *).

inline "cic:/CoRN/reals/Q_dense/Length.con".

(* UNEXPORTED
End Interval_definition
*)

inline "cic:/CoRN/reals/Q_dense/Rat_Interval.con".

(* we have this in Q_COrdField... *)

inline "cic:/CoRN/reals/Q_dense/Qlt_eq_gt_dec'.con".

(*
Lemma ex_informative_on_Q:(P:Q_as_COrdField->Prop)(Ex [q:Q_as_COrdField](P q))
                             ->{q:Q_as_COrdField | (P q)}.
Proof.
 Intro.
 Intro.
 Apply ex_informative.
 Assumption.
Qed.
*)

(* UNEXPORTED
Section COrdField_extra
*)

alias id "OF" = "cic:/CoRN/reals/Q_dense/COrdField_extra/OF.var".

inline "cic:/CoRN/reals/Q_dense/AbsSmall_pos_reflexive.con".

inline "cic:/CoRN/reals/Q_dense/AbsSmall_neg_reflexive.con".

inline "cic:/CoRN/reals/Q_dense/AbsSmall_subinterval.con".

(* UNEXPORTED
End COrdField_extra
*)

(* UNEXPORTED
Section Rational_sequence
*)

include "tactics/Opaque_algebra.ma".

(*#*** WARNING: A file is being loaded *****)

alias id "R1" = "cic:/CoRN/reals/Q_dense/Rational_sequence/R1.var".

inline "cic:/CoRN/reals/Q_dense/start_l.con".

inline "cic:/CoRN/reals/Q_dense/start_of_sequence2.con".

inline "cic:/CoRN/reals/Q_dense/start_r.con".

inline "cic:/CoRN/reals/Q_dense/start_of_sequence_property.con".

inline "cic:/CoRN/reals/Q_dense/l_less_r.con".

inline "cic:/CoRN/reals/Q_dense/shrink23.con".

inline "cic:/CoRN/reals/Q_dense/shrink13.con".

inline "cic:/CoRN/reals/Q_dense/shrink24.con".

inline "cic:/CoRN/reals/Q_dense/cotrans_analyze.con".

inline "cic:/CoRN/reals/Q_dense/cotrans_analyze_strong.con".

inline "cic:/CoRN/reals/Q_dense/trichotomy.con".

inline "cic:/CoRN/reals/Q_dense/trichotomy_strong1.con".

(* NOTATION
Notation "( A , B )" := (pairT A B).
*)

inline "cic:/CoRN/reals/Q_dense/if_cotrans.con".

inline "cic:/CoRN/reals/Q_dense/if_cotrans_strong.con".

inline "cic:/CoRN/reals/Q_dense/Intrvl.con".

inline "cic:/CoRN/reals/Q_dense/G.con".

(* UNEXPORTED
Opaque Q_as_CField.
*)

inline "cic:/CoRN/reals/Q_dense/delta_Intrvl.con".

inline "cic:/CoRN/reals/Q_dense/Length_Intrvl.con".

inline "cic:/CoRN/reals/Q_dense/Intrvl_inside_l_n.con".

inline "cic:/CoRN/reals/Q_dense/Intrvl_inside_r_n.con".

inline "cic:/CoRN/reals/Q_dense/G_m_n_lower.con".

inline "cic:/CoRN/reals/Q_dense/G_m_n_upper.con".

(* UNEXPORTED
Opaque Q_as_COrdField.
*)

inline "cic:/CoRN/reals/Q_dense/a_simple_inequality.con".

inline "cic:/CoRN/reals/Q_dense/G_conversion_rate2.con".

inline "cic:/CoRN/reals/Q_dense/CS_seq_G.con".

inline "cic:/CoRN/reals/Q_dense/G_as_CauchySeq.con".

inline "cic:/CoRN/reals/Q_dense/CS_seq_inj_Q_G.con".

inline "cic:/CoRN/reals/Q_dense/inj_Q_G_as_CauchySeq.con".

inline "cic:/CoRN/reals/Q_dense/x_in_Intrvl_l.con".

inline "cic:/CoRN/reals/Q_dense/x_in_Intrvl_r.con".

inline "cic:/CoRN/reals/Q_dense/G_conversion_rate_resp_x.con".

inline "cic:/CoRN/reals/Q_dense/x_is_SeqLimit_G.con".

(* UNEXPORTED
End Rational_sequence
*)

(* end hide *)

