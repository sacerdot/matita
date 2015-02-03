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

include "ground_1/preamble.ma".

inductive PList: Type[0] \def
| PNil: PList
| PCons: nat \to (nat \to (PList \to PList)).

let rec PConsTail (hds: PList) on hds: nat \to (nat \to PList) \def \lambda 
(h0: nat).(\lambda (d0: nat).(match hds with [PNil \Rightarrow (PCons h0 d0 
PNil) | (PCons h d hds0) \Rightarrow (let TMP_855 \def (PConsTail hds0 h0 d0) 
in (PCons h d TMP_855))])).

let rec Ss (hds: PList) on hds: PList \def match hds with [PNil \Rightarrow 
PNil | (PCons h d hds0) \Rightarrow (let TMP_857 \def (S d) in (let TMP_856 
\def (Ss hds0) in (PCons h TMP_857 TMP_856)))].

let rec papp (a: PList) on a: PList \to PList \def \lambda (b: PList).(match 
a with [PNil \Rightarrow b | (PCons h d a0) \Rightarrow (let TMP_858 \def 
(papp a0 b) in (PCons h d TMP_858))]).

