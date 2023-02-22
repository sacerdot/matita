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

include "static_2/static/lsubr.ma".

(* RESTRICTED REFINEMENT FOR LOCAL ENVIRONMENTS *****************************)

(* Main properties **********************************************************)

theorem lsubr_trans: Transitive … lsubr.
#L1 #L #H elim H -L1 -L //
[ #I #L1 #L #_ #IH #X #H elim (lsubr_inv_bind1 … H) -H *
  [ #L2 #HL2 #H | #L2 #V #W #HL2 #H1 #H2 | #I1 #I2 #L2 #V #HL2 #H1 #H2 ]
  destruct /3 width=1 by lsubr_bind, lsubr_beta, lsubr_unit/
| #L1 #L #V #W #_ #IH #X #H elim (lsubr_inv_abst1 … H) -H *
  [ #L2 #HL2 #H | #I #L2 #HL2 #H ]
  destruct /3 width=1 by lsubr_beta, lsubr_unit/
| #I1 #I2 #L1 #L #V #_ #IH #X #H elim (lsubr_inv_unit1 … H) -H
  #L2 #HL2 #H destruct /4 width=1 by lsubr_unit/
]
qed-.
