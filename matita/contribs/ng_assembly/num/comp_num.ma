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

(* ********************************************************************** *)
(*                          Progetto FreeScale                            *)
(*                                                                        *)
(*   Sviluppato da: Ing. Cosimo Oliboni, oliboni@cs.unibo.it              *)
(*   Sviluppo: 2008-2010                                                  *)
(*                                                                        *)
(* ********************************************************************** *)

include "num/exadecim.ma".

(* *********** *)
(* ESADECIMALI *)
(* *********** *)

nrecord comp_num (T:Type) : Type ≝
 {
 cnH: T;
 cnL: T
 }.

ndefinition forall_cn ≝
λT.λf:(T → bool) → bool.λP.
 f (λh.
 f (λl.
  P (mk_comp_num T h l))).

(* operatore = *)
ndefinition eq2_cn ≝
λT.λfeq:T → T → bool.
λcn1,cn2:comp_num T.
 (feq (cnH ? cn1) (cnH ? cn2)) ⊗ (feq (cnL ? cn1) (cnL ? cn2)).

ndefinition eq_cn ≝
λT.λfeq:T → bool.
λcn:comp_num T.
 (feq (cnH ? cn)) ⊗ (feq (cnL ? cn)).

(* operatore < > *)
ndefinition ltgt_cn ≝
λT.λfeq:T → T → bool.λfltgt:T → T → bool.
λcn1,cn2:comp_num T.
 (fltgt (cnH ? cn1) (cnH ? cn2)) ⊕
 ((feq (cnH ? cn1) (cnH ? cn2)) ⊗ (fltgt (cnL ? cn1) (cnL ? cn2))).

(* operatore ≤ ≥ *)
ndefinition lege_cn ≝
λT.λfeq:T → T → bool.λfltgt:T → T → bool.λflege:T → T → bool.
λcn1,cn2:comp_num T.
 (fltgt (cnH ? cn1) (cnH ? cn2)) ⊕
 ((feq (cnH ? cn1) (cnH ? cn2)) ⊗ (flege (cnL ? cn1) (cnL ? cn2))).

(* operatore cn1 op cn2 *)
ndefinition fop2_cn ≝
λT.λfop:T → T → T.
λcn1,cn2:comp_num T.
 mk_comp_num ? (fop (cnH ? cn1) (cnH ? cn2)) (fop (cnL ? cn1) (cnL ? cn2)).

ndefinition fop_cn ≝
λT.λfop:T → T.
λcn:comp_num T.
 mk_comp_num ? (fop (cnH ? cn)) (fop (cnL ? cn)).

(* operatore su parte high *)
ndefinition getOPH_cn ≝
λT.λf:T → bool.
λcn:comp_num T.
 f (cnH ? cn).

ndefinition setOPH_cn ≝
λT.λf:T → T.
λcn:comp_num T.
 mk_comp_num ? (f (cnH ? cn)) (cnL ? cn).

(* operatore su parte low *)
ndefinition getOPL_cn ≝
λT.λf:T → bool.
λcn:comp_num T.
 f (cnL ? cn).

ndefinition setOPL_cn ≝
λT.λf:T → T.
λcn:comp_num T.
 mk_comp_num ? (cnH ? cn) (f (cnL ? cn)).

(* operatore pred/succ *)
ndefinition predsucc_cn ≝
λT.λfz:T → bool.λfps:T → T.
λcn:comp_num T.
 match fz (cnL ? cn) with
  [ true ⇒ mk_comp_num ? (fps (cnH ? cn)) (fps (cnL ? cn))
  | false ⇒ mk_comp_num ? (cnH ? cn) (fps (cnL ? cn)) ]. 

(* operatore con carry applicato DX → SX *)
ndefinition opcr2_cn ≝
λT.λfopcr:bool → T → T → (ProdT bool T).
λc:bool.λcn1,cn2:comp_num T.
 match fopcr c (cnH ? cn1) (cnH ? cn2) with
  [ pair c' cnh' ⇒ match fopcr c' (cnL ? cn1) (cnL ? cn2) with
   [ pair c'' cnl' ⇒ pair … c'' (mk_comp_num ? cnh' cnl') ]].

ndefinition opcr_cn ≝
λT.λfopcr:bool → T → (ProdT bool T).
λc:bool.λcn:comp_num T.
 match fopcr c (cnH ? cn) with
  [ pair c' cnh' ⇒ match fopcr c' (cnL ? cn) with
   [ pair c'' cnl' ⇒ pair … c'' (mk_comp_num ? cnh' cnl') ]].

(* operatore con carry applicato SX → DX *)
ndefinition opcl2_cn ≝
λT.λfopcl:bool → T → T → (ProdT bool T).
λc:bool.λcn1,cn2:comp_num T.
 match fopcl c (cnL ? cn1) (cnL ? cn2) with
  [ pair c' cnl' ⇒ match fopcl c' (cnH ? cn1) (cnH ? cn2) with
   [ pair c'' cnh' ⇒ pair … c'' (mk_comp_num ? cnh' cnl') ]].

ndefinition opcl_cn ≝
λT.λfopcl:bool → T → (ProdT bool T).
λc:bool.λcn:comp_num T.
 match fopcl c (cnL ? cn) with
  [ pair c' cnl' ⇒ match fopcl c' (cnH ? cn) with
   [ pair c'' cnh' ⇒ pair … c'' (mk_comp_num ? cnh' cnl') ]].
