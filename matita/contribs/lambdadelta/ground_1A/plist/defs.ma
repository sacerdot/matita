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

include "ground_1A/preamble.ma".

inductive PList: Type[0] \def
| PNil: PList
| PCons: nat \to (nat \to (PList \to PList)).

rec definition PConsTail (hds: PList) on hds: nat \to (nat \to PList) \def 
\lambda (h0: nat).(\lambda (d0: nat).(match hds with [PNil \Rightarrow (PCons 
h0 d0 PNil) | (PCons h d hds0) \Rightarrow (PCons h d (PConsTail hds0 h0 
d0))])).

rec definition Ss (hds: PList) on hds: PList \def match hds with [PNil 
\Rightarrow PNil | (PCons h d hds0) \Rightarrow (PCons h (S d) (Ss hds0))].

rec definition papp (a: PList) on a: PList \to PList \def \lambda (b: 
PList).(match a with [PNil \Rightarrow b | (PCons h d a0) \Rightarrow (PCons 
h d (papp a0 b))]).

