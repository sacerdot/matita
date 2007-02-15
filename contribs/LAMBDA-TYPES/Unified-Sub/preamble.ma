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

(* Project started Tue Aug 22, 2006 ***************************************)

set "baseuri" "cic:/matita/LAMBDA-TYPES/Unified-Sub/preamble".

(* PREAMBLE
*)

include "logic/equality.ma".
include "../../RELATIONAL/datatypes/Bool.ma".
include "../../RELATIONAL/NPlus/props.ma".
include "../../RELATIONAL/NLE/props.ma".
include "../../RELATIONAL/NLE/nplus.ma".

axiom f_equal_3: \forall (A,B,C,D:Set).
                 \forall (f:A \to B \to C \to D). 
                 \forall (x1,x2:A).
                 \forall (y1,y2:B).
                 \forall (z1,z2:C). 
                 x1 = x2 \to y1 = y2 \to z1 = z2 \to 
                 f x1 y1 z1 = f x2 y2 z2.  
