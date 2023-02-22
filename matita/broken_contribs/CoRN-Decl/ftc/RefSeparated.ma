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

set "baseuri" "cic:/matita/CoRN-Decl/ftc/RefSeparated".

include "CoRN.ma".

(* $Id: RefSeparated.v,v 1.8 2004/04/23 10:01:00 lcf Exp $ *)

(* begin hide *)

include "ftc/COrdLemmas.ma".

include "ftc/Partitions.ma".

(* UNEXPORTED
Section Separating__Separated
*)

alias id "a" = "cic:/CoRN/ftc/RefSeparated/Separating__Separated/a.var".

alias id "b" = "cic:/CoRN/ftc/RefSeparated/Separating__Separated/b.var".

alias id "Hab" = "cic:/CoRN/ftc/RefSeparated/Separating__Separated/Hab.var".

inline "cic:/CoRN/ftc/RefSeparated/Separating__Separated/I.con" "Separating__Separated__".

alias id "F" = "cic:/CoRN/ftc/RefSeparated/Separating__Separated/F.var".

alias id "contF" = "cic:/CoRN/ftc/RefSeparated/Separating__Separated/contF.var".

alias id "incF" = "cic:/CoRN/ftc/RefSeparated/Separating__Separated/incF.var".

alias id "Hab'" = "cic:/CoRN/ftc/RefSeparated/Separating__Separated/Hab'.var".

alias id "m" = "cic:/CoRN/ftc/RefSeparated/Separating__Separated/m.var".

alias id "n" = "cic:/CoRN/ftc/RefSeparated/Separating__Separated/n.var".

alias id "P" = "cic:/CoRN/ftc/RefSeparated/Separating__Separated/P.var".

alias id "R" = "cic:/CoRN/ftc/RefSeparated/Separating__Separated/R.var".

alias id "HP" = "cic:/CoRN/ftc/RefSeparated/Separating__Separated/HP.var".

alias id "HR" = "cic:/CoRN/ftc/RefSeparated/Separating__Separated/HR.var".

inline "cic:/CoRN/ftc/RefSeparated/RS_pos_n.con".

inline "cic:/CoRN/ftc/RefSeparated/RS_pos_m.con".

alias id "alpha" = "cic:/CoRN/ftc/RefSeparated/Separating__Separated/alpha.var".

alias id "Halpha" = "cic:/CoRN/ftc/RefSeparated/Separating__Separated/Halpha.var".

inline "cic:/CoRN/ftc/RefSeparated/Separating__Separated/e.con" "Separating__Separated__".

inline "cic:/CoRN/ftc/RefSeparated/RS_He.con".

inline "cic:/CoRN/ftc/RefSeparated/Separating__Separated/contF'.con" "Separating__Separated__".

inline "cic:/CoRN/ftc/RefSeparated/Separating__Separated/d.con" "Separating__Separated__".

inline "cic:/CoRN/ftc/RefSeparated/RS_Hd.con".

inline "cic:/CoRN/ftc/RefSeparated/RS_Hd'.con".

alias id "csi" = "cic:/CoRN/ftc/RefSeparated/Separating__Separated/csi.var".

alias id "Hcsi" = "cic:/CoRN/ftc/RefSeparated/Separating__Separated/Hcsi.var".

inline "cic:/CoRN/ftc/RefSeparated/Separating__Separated/M.con" "Separating__Separated__".

inline "cic:/CoRN/ftc/RefSeparated/Separating__Separated/deltaP.con" "Separating__Separated__".

inline "cic:/CoRN/ftc/RefSeparated/Separating__Separated/deltaR.con" "Separating__Separated__".

inline "cic:/CoRN/ftc/RefSeparated/Separating__Separated/delta.con" "Separating__Separated__".

inline "cic:/CoRN/ftc/RefSeparated/RS_delta_deltaP.con".

inline "cic:/CoRN/ftc/RefSeparated/RS_delta_deltaR.con".

inline "cic:/CoRN/ftc/RefSeparated/RS_delta_csi.con".

inline "cic:/CoRN/ftc/RefSeparated/RS_delta_d.con".

inline "cic:/CoRN/ftc/RefSeparated/RS_delta_pos.con".

(* UNEXPORTED
Section Defining_ai'
*)

alias id "i" = "cic:/CoRN/ftc/RefSeparated/Separating__Separated/Defining_ai'/i.var".

alias id "Hi" = "cic:/CoRN/ftc/RefSeparated/Separating__Separated/Defining_ai'/Hi.var".

inline "cic:/CoRN/ftc/RefSeparated/separation_conseq.con".

inline "cic:/CoRN/ftc/RefSeparated/Separating__Separated/Defining_ai'/pred1.con" "Separating__Separated__Defining_ai'__".

inline "cic:/CoRN/ftc/RefSeparated/Separating__Separated/Defining_ai'/pred2.con" "Separating__Separated__Defining_ai'__".

inline "cic:/CoRN/ftc/RefSeparated/sep__sep_aux_lemma.con".

alias id "Hi0" = "cic:/CoRN/ftc/RefSeparated/Separating__Separated/Defining_ai'/Hi0.var".

alias id "Hin" = "cic:/CoRN/ftc/RefSeparated/Separating__Separated/Defining_ai'/Hin.var".

inline "cic:/CoRN/ftc/RefSeparated/sep__sep_fun_i.con".

inline "cic:/CoRN/ftc/RefSeparated/sep__sep_leEq.con".

inline "cic:/CoRN/ftc/RefSeparated/sep__sep_less.con".

inline "cic:/CoRN/ftc/RefSeparated/sep__sep_ap.con".

(* UNEXPORTED
End Defining_ai'
*)

inline "cic:/CoRN/ftc/RefSeparated/sep__sep_fun.con".

inline "cic:/CoRN/ftc/RefSeparated/sep__sep_fun_i_delta.con".

inline "cic:/CoRN/ftc/RefSeparated/sep__sep_fun_delta.con".

inline "cic:/CoRN/ftc/RefSeparated/sep__sep_mon_i.con".

inline "cic:/CoRN/ftc/RefSeparated/sep__sep_mon.con".

inline "cic:/CoRN/ftc/RefSeparated/sep__sep_fun_i_wd.con".

inline "cic:/CoRN/ftc/RefSeparated/sep__sep_fun_wd.con".

inline "cic:/CoRN/ftc/RefSeparated/sep__sep_part.con".

inline "cic:/CoRN/ftc/RefSeparated/sep__sep_lemma.con".

alias id "g" = "cic:/CoRN/ftc/RefSeparated/Separating__Separated/g.var".

alias id "gP" = "cic:/CoRN/ftc/RefSeparated/Separating__Separated/gP.var".

inline "cic:/CoRN/ftc/RefSeparated/sep__sep_points.con".

inline "cic:/CoRN/ftc/RefSeparated/sep__sep_points_lemma.con".

inline "cic:/CoRN/ftc/RefSeparated/sep__sep_aux.con".

(* NOTATION
Notation just1 := (incF _ (Pts_part_lemma _ _ _ _ _ _ gP _ _)).
*)

(* NOTATION
Notation just2 :=
  (incF _ (Pts_part_lemma _ _ _ _ _ _ sep__sep_points_lemma _ _)).
*)

inline "cic:/CoRN/ftc/RefSeparated/sep__sep_Sum.con".

inline "cic:/CoRN/ftc/RefSeparated/sep__sep_Mesh.con".

(* UNEXPORTED
End Separating__Separated
*)

(* end hide *)

