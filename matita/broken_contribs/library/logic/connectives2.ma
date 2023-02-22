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

include "higher_order_defs/relations.ma".

theorem reflexive_iff: reflexive ? iff.
 unfold reflexive;
 intro;
 split;
 intro;
 assumption.
qed.

theorem symmetric_iff: symmetric ? iff.
 unfold symmetric;
 intros;
 elim H;
 split;
 assumption.
qed.

theorem transitive_iff: transitive ? iff.
 unfold transitive;
 intros;
 elim H;
 elim H1;
 split;
 intro;
 autobatch depth=3.
qed.

