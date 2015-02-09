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

include "basic_1/lift/defs.ma".

let rec trans (hds: PList) on hds: nat \to nat \def \lambda (i: nat).(match 
hds with [PNil \Rightarrow i | (PCons h d hds0) \Rightarrow (let j \def 
(trans hds0 i) in (let TMP_1 \def (blt j d) in (match TMP_1 with [true 
\Rightarrow j | false \Rightarrow (plus j h)])))]).

let rec lift1 (hds: PList) on hds: T \to T \def \lambda (t: T).(match hds 
with [PNil \Rightarrow t | (PCons h d hds0) \Rightarrow (let TMP_1 \def 
(lift1 hds0 t) in (lift h d TMP_1))]).

let rec lifts1 (hds: PList) (ts: TList) on ts: TList \def match ts with [TNil 
\Rightarrow TNil | (TCons t ts0) \Rightarrow (let TMP_1 \def (lift1 hds t) in 
(let TMP_2 \def (lifts1 hds ts0) in (TCons TMP_1 TMP_2)))].

