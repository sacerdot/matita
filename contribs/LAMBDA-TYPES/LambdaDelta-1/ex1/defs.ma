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

set "baseuri" "cic:/matita/LAMBDA-TYPES/LambdaDelta-1/ex1/defs".

include "C/defs.ma".

definition ex1_c:
 C
\def
 CHead (CHead (CHead (CSort O) (Bind Abst) (TSort O)) (Bind Abst) (TSort O)) 
(Bind Abst) (TLRef O).

definition ex1_t:
 T
\def
 THead (Flat Appl) (TLRef O) (THead (Bind Abst) (TLRef (S (S O))) (TSort O)).

