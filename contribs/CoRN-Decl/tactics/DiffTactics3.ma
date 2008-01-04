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

set "baseuri" "cic:/matita/CoRN-Decl/tactics/DiffTactics3".

include "CoRN.ma".

(* $Id: DiffTactics3.v,v 1.1.1.1 2004/02/05 16:25:44 lionelm Exp $ *)

(* begin hide *)

include "ftc/MoreFunSeries.ma".

include "ftc/Composition.ma".

include "tactics/DiffTactics2.ma".

(* UNEXPORTED
Ltac Deriv_substR :=
  match goal with
  |  |- (Derivative ?X1 _) =>
      let t := derivative_of X1 in
      apply Derivative_wdr with t
  end.
*)

inline "cic:/CoRN/tactics/DiffTactics3/symbPF.ind".

(*
  | ssum0     : nat->(nat->symbPF)->symbPF
  | ssumx     : (n:nat)((i:nat)(lt i n)->symbPF)->symbPF
  | ssum      : nat->nat->(nat->symbPF)->symbPF
*)

inline "cic:/CoRN/tactics/DiffTactics3/symb_to_PartIR.con".

inline "cic:/CoRN/tactics/DiffTactics3/symbPF_deriv.con".

(* UNEXPORTED
Ltac PartIR_to_symbPF f :=
  match constr:f with
  | ([-C-]?X3) => constr:(sconst X3)
  | FId => constr:sid
  | (?X3{+}?X4) =>
      let t1 := PartIR_to_symbPF X3 with t2 := PartIR_to_symbPF X4 in
      constr:(splus t1 t2)
  | ({--}?X3) =>
      let t1 := PartIR_to_symbPF X3 in
      constr:(sinv t1)
  | (?X3{-}?X4) =>
      let t1 := PartIR_to_symbPF X3 with t2 := PartIR_to_symbPF X4 in
      constr:(sminus t1 t2)
  | (?X3{*}?X4) =>
      let t1 := PartIR_to_symbPF X3 with t2 := PartIR_to_symbPF X4 in
      constr:(smult t1 t2)
  | (?X3{**}?X4) =>
      let t := PartIR_to_symbPF X4 in
      constr:(sscalmult X3 t)
  | (?X3{^}?X4) =>
      let t1 := PartIR_to_symbPF X3 in
      constr:(snth t1 X4)
  | ({1/}?X3) =>
      let t1 := PartIR_to_symbPF X3 in
      constr:(srecip t1)
  | (?X3{/}?X4) =>
      let t1 := PartIR_to_symbPF X3 with t2 := PartIR_to_symbPF X4 in
      constr:(sdiv t1 t2)
  | (?X3[o]?X4) =>
      let t1 := PartIR_to_symbPF X3 with t2 := PartIR_to_symbPF X4 in
      constr:(scomp t1 t2)
  | ?X3 =>
      let t := constr:X3 in
      match goal with
      | H:(Derivative ?X1 ?X2 t ?X4) |- _ =>
          constr:(shyp X1 X2 t X4 H)
      | H:(Diffble ?X1 ?X2 t) |- _ => constr:(shyp' X1 X2 t H)
      end
  end.
*)

(* UNEXPORTED
Ltac Derivative_Help :=
  match goal with
  |  |- (Derivative ?X1 ?X2 ?X3 ?X4) =>
      let r := PartIR_to_symbPF X3 in
      (apply Derivative_wdr with (symbPF_deriv r);
        [ unfold symbPF_deriv, symb_to_PartIR in |- *
        | simpl in |- *; Deriv ])
  end.
*)

(* end hide *)

