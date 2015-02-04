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

include "basic_1/preamble.ma".

inductive B: Type[0] \def
| Abbr: B
| Abst: B
| Void: B.

inductive F: Type[0] \def
| Appl: F
| Cast: F.

inductive K: Type[0] \def
| Bind: B \to K
| Flat: F \to K.

inductive T: Type[0] \def
| TSort: nat \to T
| TLRef: nat \to T
| THead: K \to (T \to (T \to T)).

let rec tweight (t: T) on t: nat \def match t with [(TSort _) \Rightarrow (S 
O) | (TLRef _) \Rightarrow (S O) | (THead _ u t0) \Rightarrow (let TMP_1 \def 
(tweight u) in (let TMP_2 \def (tweight t0) in (let TMP_3 \def (plus TMP_1 
TMP_2) in (S TMP_3))))].
