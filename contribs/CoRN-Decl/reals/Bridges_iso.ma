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

set "baseuri" "cic:/matita/CoRN-Decl/reals/Bridges_iso".

include "CoRN.ma".

(* begin hide *)

(* file        : bridges_gives_our.v                               *)

(* version     : 1.50 - 09/05/2001                                 *)

(* version     : 1.00 - 09/03/2001                                 *)

(* author      : Milad Niqui                                       *)

(* language    : coq7.0bet26feb                                    *)

(* dependency  : least_upper_bound_principle                       *)

(* description : Bridges' proof of Cauchy completeness in TCS-219  *)

include "reals/Bridges_LUB.ma".

(* This lemma comes from lemmas.v of Martijn Oostdijk *)

inline "cic:/CoRN/reals/Bridges_iso/le_witness_informative.con".

(* UNEXPORTED
Section bridges_axioms_imply_ours
*)

alias id "OF" = "cic:/CoRN/reals/Bridges_iso/bridges_axioms_imply_ours/OF.var".

alias id "lubp" = "cic:/CoRN/reals/Bridges_iso/bridges_axioms_imply_ours/lubp.var".

alias id "is_Archimedes" = "cic:/CoRN/reals/Bridges_iso/bridges_axioms_imply_ours/is_Archimedes.var".

inline "cic:/CoRN/reals/Bridges_iso/is_Archimedes'.con".

(* UNEXPORTED
Section proofs_in_TCS
*)

inline "cic:/CoRN/reals/Bridges_iso/leEq_geEq.con".

inline "cic:/CoRN/reals/Bridges_iso/glbp.con".

(* UNEXPORTED
Section supremum
*)

alias id "P" = "cic:/CoRN/reals/Bridges_iso/bridges_axioms_imply_ours/proofs_in_TCS/supremum/P.var".

inline "cic:/CoRN/reals/Bridges_iso/inequality1.con".

inline "cic:/CoRN/reals/Bridges_iso/inequality2.con".

inline "cic:/CoRN/reals/Bridges_iso/inequality3.con".

inline "cic:/CoRN/reals/Bridges_iso/inequality4.con".

inline "cic:/CoRN/reals/Bridges_iso/Hum.con".

inline "cic:/CoRN/reals/Bridges_iso/bound_tk1.con".

inline "cic:/CoRN/reals/Bridges_iso/bound_tk2.con".

inline "cic:/CoRN/reals/Bridges_iso/trick.con".

inline "cic:/CoRN/reals/Bridges_iso/trick'.con".

inline "cic:/CoRN/reals/Bridges_iso/up_bound_for_n_element.con".

inline "cic:/CoRN/reals/Bridges_iso/low_bound_for_n_element.con".

inline "cic:/CoRN/reals/Bridges_iso/saghf.con".

inline "cic:/CoRN/reals/Bridges_iso/Psaghf.con".

inline "cic:/CoRN/reals/Bridges_iso/kaf.con".

inline "cic:/CoRN/reals/Bridges_iso/Pkaf.con".

alias id "is_finite_P" = "cic:/CoRN/reals/Bridges_iso/bridges_axioms_imply_ours/proofs_in_TCS/supremum/is_finite_P.var".

inline "cic:/CoRN/reals/Bridges_iso/card.con".

inline "cic:/CoRN/reals/Bridges_iso/Pcard1.con".

inline "cic:/CoRN/reals/Bridges_iso/seq.con".

inline "cic:/CoRN/reals/Bridges_iso/Pseq1.con".

inline "cic:/CoRN/reals/Bridges_iso/Pseq1_unfolded.con".

inline "cic:/CoRN/reals/Bridges_iso/indeks.con".

inline "cic:/CoRN/reals/Bridges_iso/Pindeks.con".

alias id "is_onto_seq_P" = "cic:/CoRN/reals/Bridges_iso/bridges_axioms_imply_ours/proofs_in_TCS/supremum/is_onto_seq_P.var".

inline "cic:/CoRN/reals/Bridges_iso/P_is_inhabited.con".

(*
Lemma bounded_quantifier:(N:nat;phi,psi:nat->Prop)
                 ((m:nat)(le m N)->(phi m)\/(psi m))->
        ((m:nat)(le m N)->(phi m))\/(Ex [j:nat](le j N)/\(psi j)).
Proof.
 Intros.
 Induction N.
 Cut (phi O)\/(psi O).
 Intro.
 Case H0.
 Intros.
 Left.
 Intros.
 Rewrite <- (le_n_O_eq m H2).
 Assumption.
 Intro.
 Right.
 Exists O.
 Split.
 Constructor.
 Assumption.
 Apply H.
 Constructor.*)

(* n=(S n0) *)

(* Case HrecN.
 Intros.
 Apply H.
 Apply le_trans with m:=N.
 Assumption.
 Apply le_n_Sn.
 Intro.
 Case (H (S N)).
 Apply le_n.
 Intros.
 Left.
 Intros.
 Case (le_lt_eq_dec m (S N)).
 Assumption.
 Intros.
 Apply H0.
 Apply (lt_n_Sm_le m N).
 Assumption.
 Intro.
 Rewrite e.
 Assumption.
 Intro.
 Right.
 Exists (S N).
 Split.
 Apply le_n.
 Assumption.
 Intro.
 Right.
 Case H0.
 Intro j.
 Intros.
 Exists j.
 Elim H1.
 Intros.
 Split.
 Apply le_trans with m:=N.
 Assumption.
 Apply le_n_Sn.
 Assumption.
Qed. 
*)

inline "cic:/CoRN/reals/Bridges_iso/bounded_quantifier_informative.con".

inline "cic:/CoRN/reals/Bridges_iso/bridges_lemma1a.con".

alias id "P_is_strongly_extensional" = "cic:/CoRN/reals/Bridges_iso/bridges_axioms_imply_ours/proofs_in_TCS/supremum/P_is_strongly_extensional.var".

inline "cic:/CoRN/reals/Bridges_iso/bridges_lemma1b.con".

(* UNEXPORTED
End supremum
*)

(*#**********************************)

(*#**********************************)

(*#**********************************)

(*#**********************************)

(* UNEXPORTED
Section Every_Cauchy_Sequence_is_bounded
*)

inline "cic:/CoRN/reals/Bridges_iso/seq2set.con".

alias id "g" = "cic:/CoRN/reals/Bridges_iso/bridges_axioms_imply_ours/proofs_in_TCS/Every_Cauchy_Sequence_is_bounded/g.var".

inline "cic:/CoRN/reals/Bridges_iso/bridges_axioms_imply_ours/proofs_in_TCS/Every_Cauchy_Sequence_is_bounded/g_.con" "bridges_axioms_imply_ours__proofs_in_TCS__Every_Cauchy_Sequence_is_bounded__".

inline "cic:/CoRN/reals/Bridges_iso/bridges_axioms_imply_ours/proofs_in_TCS/Every_Cauchy_Sequence_is_bounded/pg.con" "bridges_axioms_imply_ours__proofs_in_TCS__Every_Cauchy_Sequence_is_bounded__".

inline "cic:/CoRN/reals/Bridges_iso/bridges_axioms_imply_ours/proofs_in_TCS/Every_Cauchy_Sequence_is_bounded/P.con" "bridges_axioms_imply_ours__proofs_in_TCS__Every_Cauchy_Sequence_is_bounded__".

inline "cic:/CoRN/reals/Bridges_iso/fin_is_fin.con".

inline "cic:/CoRN/reals/Bridges_iso/card_fin.con".

inline "cic:/CoRN/reals/Bridges_iso/finite_seq.con".

inline "cic:/CoRN/reals/Bridges_iso/bridges_lemma2a.con".

inline "cic:/CoRN/reals/Bridges_iso/sup.con".

inline "cic:/CoRN/reals/Bridges_iso/Psup.con".

inline "cic:/CoRN/reals/Bridges_iso/Psup_proj1.con".

inline "cic:/CoRN/reals/Bridges_iso/Psup_unfolded1.con".

inline "cic:/CoRN/reals/Bridges_iso/Psup_unfolded2.con".

inline "cic:/CoRN/reals/Bridges_iso/bridges_lemma2b.con".

inline "cic:/CoRN/reals/Bridges_iso/inf.con".

inline "cic:/CoRN/reals/Bridges_iso/Pinf.con".

inline "cic:/CoRN/reals/Bridges_iso/Pinf_proj1.con".

inline "cic:/CoRN/reals/Bridges_iso/Pinf_unfolded1.con".

inline "cic:/CoRN/reals/Bridges_iso/Pinf_unfolded2.con".

(* I tried very much not to mention this lemma! *)

inline "cic:/CoRN/reals/Bridges_iso/sup_leEq.con".

inline "cic:/CoRN/reals/Bridges_iso/inf_geEq.con".

inline "cic:/CoRN/reals/Bridges_iso/tail_is_Cauchy.con".

inline "cic:/CoRN/reals/Bridges_iso/tail_seq.con".

(* UNEXPORTED
End Every_Cauchy_Sequence_is_bounded
*)

alias id "g" = "cic:/CoRN/reals/Bridges_iso/bridges_axioms_imply_ours/proofs_in_TCS/g.var".

inline "cic:/CoRN/reals/Bridges_iso/bridges_axioms_imply_ours/proofs_in_TCS/g_.con" "bridges_axioms_imply_ours__proofs_in_TCS__".

inline "cic:/CoRN/reals/Bridges_iso/bridges_axioms_imply_ours/proofs_in_TCS/pg.con" "bridges_axioms_imply_ours__proofs_in_TCS__".

inline "cic:/CoRN/reals/Bridges_iso/bridges_axioms_imply_ours/proofs_in_TCS/sup_tail.con" "bridges_axioms_imply_ours__proofs_in_TCS__".

inline "cic:/CoRN/reals/Bridges_iso/sup_tail_leEq.con".

inline "cic:/CoRN/reals/Bridges_iso/sup_tail_is_Cauchy.con".

inline "cic:/CoRN/reals/Bridges_iso/sup_tail_as_Cauchy.con".

inline "cic:/CoRN/reals/Bridges_iso/bridges_axioms_imply_ours/proofs_in_TCS/L.con" "bridges_axioms_imply_ours__proofs_in_TCS__".

inline "cic:/CoRN/reals/Bridges_iso/sup_tail_decrease.con".

inline "cic:/CoRN/reals/Bridges_iso/L_less_sup_n.con".

inline "cic:/CoRN/reals/Bridges_iso/Psup_unfolded2_informative.con".

inline "cic:/CoRN/reals/Bridges_iso/Pinf_unfolded2_informative.con".

inline "cic:/CoRN/reals/Bridges_iso/convergent_subseq.con".

(* very elegant proof almost as short as text version! *)

inline "cic:/CoRN/reals/Bridges_iso/lubp_gives_Cauchy.con".

(* UNEXPORTED
End proofs_in_TCS
*)

inline "cic:/CoRN/reals/Bridges_iso/Bridges_R_is_CReals.con".

inline "cic:/CoRN/reals/Bridges_iso/Bridges_R_as_CReals.con".

(* UNEXPORTED
End bridges_axioms_imply_ours
*)

(* end hide *)

(*#* remove printing Q *)

