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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Base-2/preamble".

include "../Base-1/definitions.ma".

default "equality"
 cic:/Coq/Init/Logic/eq.ind
 cic:/matita/LAMBDA-TYPES/Base-1/preamble/sym_eq.con
 cic:/matita/LAMBDA-TYPES/Base-1/preamble/trans_eq.con
 cic:/Coq/Init/Logic/eq_ind.con
 cic:/Coq/Init/Logic/eq_ind_r.con
 cic:/Coq/Init/Logic/eq_rec.con
 cic:/Coq/Init/Logic/eq_rec_r.con
 cic:/Coq/Init/Logic/eq_rect.con
 cic:/Coq/Init/Logic/eq_rect_r.con
 cic:/matita/LAMBDA-TYPES/Base-1/preamble/f_equal.con
 cic:/matita/legacy/coq/f_equal1.con.
