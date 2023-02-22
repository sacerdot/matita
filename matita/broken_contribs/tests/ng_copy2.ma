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

include "ng_copy.ma".

ncopy cic:/matita/tests/ng_copy/
suffix 1
change cic:/matita/pts/Type1.univ with cic:/matita/pts/Type2.univ
change cic:/matita/pts/Type1.univ with cic:/matita/pts/Type2.univ
change cic:/matita/pts/Type1.univ with cic:/matita/pts/Type2.univ
