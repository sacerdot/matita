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

set "baseuri" "cic:/matita/CoRN-Decl/tactics/DiffTactics2".

include "CoRN.ma".

(* $Id: DiffTactics2.v,v 1.1.1.1 2004/02/05 16:25:45 lionelm Exp $ *)

(* begin hide *)

include "ftc/Differentiability.ma".

(* UNEXPORTED
Section Automatizing_Continuity
*)

alias id "a" = "cic:/CoRN/tactics/DiffTactics2/Automatizing_Continuity/a.var".

alias id "b" = "cic:/CoRN/tactics/DiffTactics2/Automatizing_Continuity/b.var".

inline "cic:/CoRN/tactics/DiffTactics2/cont_function.ind".

inline "cic:/CoRN/tactics/DiffTactics2/cont_to_pfunct.con".

inline "cic:/CoRN/tactics/DiffTactics2/continuous_cont.con".

(* UNEXPORTED
End Automatizing_Continuity
*)

(* UNEXPORTED
Ltac pfunct_to_cont a b f :=
  match constr:f with
  | ([-C-]?X3) => constr:(cconst a b X3)
  | FId => constr:(cid a b)
  | (?X3{+}?X4) =>
      let t1 := pfunct_to_cont a b X3 with t2 := pfunct_to_cont a b X4 in
      constr:(cplus a b t1 t2)
  | ({--}?X3) =>
      let t1 := pfunct_to_cont a b X3 in
      constr:(cinv a b t1)
  | (?X3{-}?X4) =>
      let t1 := pfunct_to_cont a b X3 with t2 := pfunct_to_cont a b X4 in
      constr:(cminus a b t1 t2)
  | (?X3{*}?X4) =>
      let t1 := pfunct_to_cont a b X3 with t2 := pfunct_to_cont a b X4 in
      constr:(cmult a b t1 t2)
  | (?X3{**}?X4) =>
      let t := pfunct_to_cont a b X4 in
      constr:(cscalmult a b X3 t)
  | (?X3{^}?X4) =>
      let t1 := pfunct_to_cont a b X3 in
      constr:(cnth a b t1 X4)
  | (FAbs ?X3) => let t1 := pfunct_to_cont a b X3 in
                  constr:(cabs a b t1)
  | ?X3 =>
      let t := constr:X3 in
      match goal with
      | Hab:_,H:(Continuous_I (a:=a) (b:=b) ?X1 t) |- _ =>
          constr:(hyp_c a b X1 t H)
      | H:(Derivative_I (a:=a) (b:=b) ?X1 t ?X4) |- _ =>
          constr:(hyp_d a b X1 t X4 H)
      | H:(Derivative_I (a:=a) (b:=b) ?X1 ?X4 t) |- _ =>
          constr:(hyp_d' a b X1 X4 t H)
      | H:(Diffble_I (a:=a) (b:=b) ?X1 t) |- _ =>
          constr:(hyp_diff a b X1 t H)
      end
  end.
*)

(* UNEXPORTED
Ltac New_Contin :=
  match goal with
  |  |- (Continuous_I (a:=?X1) (b:=?X2) ?X4 ?X3) =>
      let r := pfunct_to_cont X1 X2 X3 in
      let a := constr:X1 in
      let b := constr:X2 in
      (apply Continuous_I_wd with (cont_to_pfunct a b r);
        [ unfold cont_to_pfunct in |- * | apply continuous_cont ])
  end.
*)

(* UNEXPORTED
Section Automatizing_Derivatives
*)

alias id "a" = "cic:/CoRN/tactics/DiffTactics2/Automatizing_Derivatives/a.var".

alias id "b" = "cic:/CoRN/tactics/DiffTactics2/Automatizing_Derivatives/b.var".

inline "cic:/CoRN/tactics/DiffTactics2/deriv_function.ind".

inline "cic:/CoRN/tactics/DiffTactics2/deriv_to_pfunct.con".

inline "cic:/CoRN/tactics/DiffTactics2/deriv_deriv.con".

inline "cic:/CoRN/tactics/DiffTactics2/deriv_restr.con".

inline "cic:/CoRN/tactics/DiffTactics2/diffble_restr.con".

(* UNEXPORTED
End Automatizing_Derivatives
*)

(* UNEXPORTED
Ltac pfunct_to_restr a b f :=
  match constr:f with
  | ([-C-]?X3) => constr:(const a b X3)
  | FId => constr:(id a b)
  | (?X3{+}?X4) =>
      let t1 := pfunct_to_restr a b X3 with t2 := pfunct_to_restr a b X4 in
      constr:(rplus a b t1 t2)
  | ({--}?X3) =>
      let t1 := pfunct_to_restr a b X3 in
      constr:(rinv a b t1)
  | (?X3{-}?X4) =>
      let t1 := pfunct_to_restr a b X3 with t2 := pfunct_to_restr a b X4 in
      constr:(rminus a b t1 t2)
  | (?X3{*}?X4) =>
      let t1 := pfunct_to_restr a b X3 with t2 := pfunct_to_restr a b X4 in
      constr:(rmult a b t1 t2)
  | (?X3{**}?X4) =>
      let t := pfunct_to_restr a b X4 in
      constr:(rscalmult a b X3 t)
  | (?X3{^}?X4) =>
      let t1 := pfunct_to_restr a b X3 in
      constr:(rnth a b t1 X4)
  | ?X3 =>
      let t := constr:X3 in
      match goal with
      | H:(Derivative_I (a:=a) (b:=b) ?X1 t ?X4) |- _ =>
          constr:(hyp a b X1 t X4 H)
      | H:(Diffble_I (a:=a) (b:=b) ?X1 t) |- _ => constr:(
      hyp' a b X1 t H)
      end
  end.
*)

(* UNEXPORTED
Ltac New_Deriv :=
  match goal with
  |  |- (Derivative_I (a:=?X1) (b:=?X2) _ ?X3 ?X4) =>
      let r := pfunct_to_restr X1 X2 X3 in
      (apply Derivative_I_wdl with (deriv_to_pfunct X1 X2 r);
        [ unfold deriv_to_pfunct in |- *
        | apply Derivative_I_wdr with (deriv_deriv X1 X2 r);
           [ unfold deriv_deriv, deriv_to_pfunct in |- *
           | apply deriv_restr ] ])
  end.
*)

(* UNEXPORTED
Ltac Differentiate :=
  match goal with
  |  |- (Diffble_I (a:=?X1) (b:=?X2) _ ?X3) =>
      let r := pfunct_to_restr X1 X2 X3 in
      (apply Diffble_I_wd with (deriv_to_pfunct X1 X2 r);
        [ apply diffble_restr | unfold deriv_deriv, deriv_to_pfunct in |- * ])
  end.
*)

(* UNEXPORTED
Ltac derivative_of f :=
  match constr:f with
  | ([-C-]?X3) => constr:([-C-]ZeroR)
  | FId => constr:([-C-]OneR)
  | (?X3{+}?X4) =>
      let t1 := derivative_of X3 with t2 := derivative_of X4 in
      constr:(t1{+}t2)
  | ({--}?X3) => let t1 := derivative_of X3 in
                 constr:({--}t1)
  | (?X3{-}?X4) =>
      let t1 := derivative_of X3 with t2 := derivative_of X4 in
      constr:(t1{-}t2)
  | (?X3{*}?X4) =>
      let t1 := derivative_of X3
      with t2 := derivative_of X4
      with t3 := constr:X3
      with t4 := constr:X4 in
      constr:(t3{*}t2{+}t1{*}t4)
  | (?X3{**}?X4) =>
      let t1 := derivative_of X4 with t2 := constr:X3 in
      constr:(t2{**}t1)
  | (?X3{^}0) => constr:([-C-]ZeroR)
  | (?X3{^}S ?X4) =>
      let t1 := derivative_of X3 with t2 := constr:X3 with t3 := constr:X4 in
      constr:(nring _ (S t3){**}(t1{*}t2{^}t3))
  | ({1/}?X3) =>
      let t1 := derivative_of X3 with t2 := constr:X3 in
      constr:({--}(t1{/}t2{*}t2))
  | (?X3{/}?X4) =>
      let t1 := derivative_of X3
      with t2 := derivative_of X4
      with t3 := constr:X3
      with t4 := constr:X4 in
      constr:((t1{*}t4{-}t3{*}t2){/}t4{*}t4)
  | (?X3[o]?X4) =>
      let t1 := derivative_of X3
      with t2 := derivative_of X4
      with t3 := constr:X3 in
      constr:((t3[o]t2){*}t1)
  | ?X3 =>
      let t := constr:X3 in
      match goal with
      | H:(Derivative_I (b:=t) ?X4) |- _ =>
          let t1 := constr:X4 in
          constr:t1
      end
  end.
*)

(* UNEXPORTED
Ltac Deriv_I_substR :=
  match goal with
  |  |- (Derivative_I _ ?X1 _) =>
      let t := derivative_of X1 in
      apply Derivative_I_wdr with t
  end.
*)

(* end hide *)

