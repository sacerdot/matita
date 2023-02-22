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

set "baseuri" "cic:/matita/CoRN-Decl/ftc/RefSeparating".

include "CoRN.ma".

(* $Id: RefSeparating.v,v 1.7 2004/04/23 10:01:01 lcf Exp $ *)

(* begin hide *)

include "ftc/COrdLemmas.ma".

include "ftc/Partitions.ma".

(* UNEXPORTED
Section Separating_Partition
*)

alias id "a" = "cic:/CoRN/ftc/RefSeparating/Separating_Partition/a.var".

alias id "b" = "cic:/CoRN/ftc/RefSeparating/Separating_Partition/b.var".

alias id "Hab" = "cic:/CoRN/ftc/RefSeparating/Separating_Partition/Hab.var".

inline "cic:/CoRN/ftc/RefSeparating/Separating_Partition/I.con" "Separating_Partition__".

alias id "F" = "cic:/CoRN/ftc/RefSeparating/Separating_Partition/F.var".

alias id "contF" = "cic:/CoRN/ftc/RefSeparating/Separating_Partition/contF.var".

alias id "incF" = "cic:/CoRN/ftc/RefSeparating/Separating_Partition/incF.var".

alias id "Hab'" = "cic:/CoRN/ftc/RefSeparating/Separating_Partition/Hab'.var".

alias id "n" = "cic:/CoRN/ftc/RefSeparating/Separating_Partition/n.var".

alias id "P" = "cic:/CoRN/ftc/RefSeparating/Separating_Partition/P.var".

alias id "alpha" = "cic:/CoRN/ftc/RefSeparating/Separating_Partition/alpha.var".

alias id "Halpha" = "cic:/CoRN/ftc/RefSeparating/Separating_Partition/Halpha.var".

alias id "csi" = "cic:/CoRN/ftc/RefSeparating/Separating_Partition/csi.var".

alias id "Hcsi" = "cic:/CoRN/ftc/RefSeparating/Separating_Partition/Hcsi.var".

inline "cic:/CoRN/ftc/RefSeparating/Separating_Partition/M.con" "Separating_Partition__".

inline "cic:/CoRN/ftc/RefSeparating/RS'_pos_n.con".

inline "cic:/CoRN/ftc/RefSeparating/SPap_n.con".

inline "cic:/CoRN/ftc/RefSeparating/Separating_Partition/delta.con" "Separating_Partition__".

inline "cic:/CoRN/ftc/RefSeparating/RS'_delta_pos.con".

inline "cic:/CoRN/ftc/RefSeparating/RS'_delta_csi.con".

alias id "Hab''" = "cic:/CoRN/ftc/RefSeparating/Separating_Partition/Hab''.var".

inline "cic:/CoRN/ftc/RefSeparating/sep__part_lemma.con".

inline "cic:/CoRN/ftc/RefSeparating/sep__part_h.con".

inline "cic:/CoRN/ftc/RefSeparating/sep__part_h_bnd.con".

inline "cic:/CoRN/ftc/RefSeparating/sep__part_h_mon_1.con".

inline "cic:/CoRN/ftc/RefSeparating/sep__part_h_mon_2.con".

inline "cic:/CoRN/ftc/RefSeparating/sep__part_h_mon_3.con".

inline "cic:/CoRN/ftc/RefSeparating/sep__part_app_n.con".

inline "cic:/CoRN/ftc/RefSeparating/sep__part_h_lemma.con".

inline "cic:/CoRN/ftc/RefSeparating/sep__part_h_lemma2.con".

inline "cic:/CoRN/ftc/RefSeparating/sep__part_h_lemma3.con".

inline "cic:/CoRN/ftc/RefSeparating/RS'_delta2_delta4.con".

inline "cic:/CoRN/ftc/RefSeparating/RS'_m1.con".

inline "cic:/CoRN/ftc/RefSeparating/RS'_m.con".

(* NOTATION
Notation m := RS'_m.
*)

inline "cic:/CoRN/ftc/RefSeparating/sep__part_length.con".

inline "cic:/CoRN/ftc/RefSeparating/RS'_m_m1.con".

inline "cic:/CoRN/ftc/RefSeparating/RS'_pos_m.con".

inline "cic:/CoRN/ftc/RefSeparating/sep__part_fun.con".

inline "cic:/CoRN/ftc/RefSeparating/sep__part_fun_bnd.con".

inline "cic:/CoRN/ftc/RefSeparating/sep__part_fun_0.con".

inline "cic:/CoRN/ftc/RefSeparating/sep__part_fun_i.con".

inline "cic:/CoRN/ftc/RefSeparating/sep__part_fun_m.con".

inline "cic:/CoRN/ftc/RefSeparating/sep__part_fun_i'.con".

inline "cic:/CoRN/ftc/RefSeparating/sep__part_fun_bnd'.con".

inline "cic:/CoRN/ftc/RefSeparating/sep__part_fun_wd.con".

inline "cic:/CoRN/ftc/RefSeparating/sep__part_fun_mon.con".

inline "cic:/CoRN/ftc/RefSeparating/sep__part.con".

inline "cic:/CoRN/ftc/RefSeparating/sep__part_fun_mon_pts.con".

inline "cic:/CoRN/ftc/RefSeparating/sep__part_mon.con".

inline "cic:/CoRN/ftc/RefSeparating/sep__part_mon_Mesh.con".

alias id "g" = "cic:/CoRN/ftc/RefSeparating/Separating_Partition/g.var".

alias id "gP" = "cic:/CoRN/ftc/RefSeparating/Separating_Partition/gP.var".

alias id "gP'" = "cic:/CoRN/ftc/RefSeparating/Separating_Partition/gP'.var".

inline "cic:/CoRN/ftc/RefSeparating/sep__part_pts.con".

inline "cic:/CoRN/ftc/RefSeparating/sep__part_pts_lemma.con".

inline "cic:/CoRN/ftc/RefSeparating/sep__part_pts_in_Partition.con".

inline "cic:/CoRN/ftc/RefSeparating/RS'_Hsep_S.con".

inline "cic:/CoRN/ftc/RefSeparating/RS'_Hsep.con".

inline "cic:/CoRN/ftc/RefSeparating/RS'_h.con".

(* NOTATION
Notation h := RS'_h.
*)

(* NOTATION
Notation just1 := (incF _ (Pts_part_lemma _ _ _ _ _ _ gP _ _)).
*)

(* NOTATION
Notation just2 :=
  (incF _ (Pts_part_lemma _ _ _ _ _ _ sep__part_pts_in_Partition _ _)).
*)

inline "cic:/CoRN/ftc/RefSeparating/sep__part_suRS'_m1.con".

inline "cic:/CoRN/ftc/RefSeparating/sep__part_Sum2.con".

inline "cic:/CoRN/ftc/RefSeparating/sep__part_Sum3.con".

inline "cic:/CoRN/ftc/RefSeparating/sep__part_Sum4.con".

inline "cic:/CoRN/ftc/RefSeparating/sep__part_aux.con".

inline "cic:/CoRN/ftc/RefSeparating/sep__part_Sum.con".

(* UNEXPORTED
End Separating_Partition
*)

(* end hide *)

