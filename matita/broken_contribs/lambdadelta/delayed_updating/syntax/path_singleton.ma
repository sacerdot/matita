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

include "ground/lib/list_singleton_rcons.ma".
include "delayed_updating/notation/functions/power_2.ma".
include "delayed_updating/syntax/path.ma".

(* SINGLETON FOR PATH *******************************************************)

interpretation
  "singleton (path)"
  'Power l n = (list_singleton n label l).
