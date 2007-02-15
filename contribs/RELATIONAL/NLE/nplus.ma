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

set "baseuri" "cic:/matita/RELATIONAL/NLE/nplus".

include "NLE/defs.ma".

axiom nle_nplus_comp: \forall x1, x2, x3. (x1 + x2 == x3) \to
                      \forall y1, y2, y3. (y1 + y2 == y3) \to
                      x1 <= y1 \to x2 <= y2 \to x3 <= y3.

axiom nle_nplus_comp_lt_2: \forall x1, x2, x3. (x1 + x2 == x3) \to
                           \forall y1, y2, y3. (y1 + y2 == y3) \to
                           x1 <= y1 \to x2 < y2 \to x3 < y3.
