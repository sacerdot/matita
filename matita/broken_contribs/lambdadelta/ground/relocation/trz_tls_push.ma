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

include "ground/relocation/trz_tls.ma".
include "ground/relocation/trz_push.ma".

(* ITERATED TAIL FOR TOTAL RELOCATION MAPS WITH INTEGERS ********************)

(* Constructions with trz_push **********************************************)

lemma trz_tls_pos_unit_push (f):
      f ≐ ⫰*[⁤𝟏]⫯f.
#f #z0 <trz_tls_unfold <trz_push_pos_unit
cases z0 -z0 [ * [| #p ]|| #p ]
[ 
