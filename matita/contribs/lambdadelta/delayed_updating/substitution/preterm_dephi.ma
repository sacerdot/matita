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

include "delayed_updating/syntax/path_dephi.ma".
include "delayed_updating/syntax/preterm_constructors.ma".

(* DEPHI FOR PRETERM ********************************************************)

definition preterm_dephi (f) (t): preterm ≝
           λp. ∃∃q. q ϵ t & p = path_dephi f q. 
