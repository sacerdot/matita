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

include "ground/lib/list_rcons.ma".
include "ground/lib/list_singleton_append.ma".

(* SINGLETON FOR LISTS ******************************************************)

(* Constructions with list_rcons ********************************************)

lemma list_singleton_succ_rcons (A) (a) (n):
      a^n ⨭ a = a^{A}(⁤↑n).
#A #a #n
>nplus_unit_sn >list_singleton_append //
qed.

lemma list_singleton_cons_shift (A) (a) (n):
      a ⨮ a^n = a^n ⨭{A} a.
#A #a #n //
qed.
